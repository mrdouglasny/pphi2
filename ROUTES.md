# P(φ)₂ Interacting Measure Constructions

Three constructions of interacting P(φ)₂ measures on three spacetimes.
All share the general framework (`InteractingMeasure/General.lean`):

```
dμ_V = (1/Z) exp(-V) dμ_free,   Z = ∫ exp(-V) dμ_free
```

---

## Route A: Lattice → Euclidean ℝ²

**Purpose:** Main theorem — existence of P(φ)₂ QFT satisfying OS0–OS4.

**Spacetime:** ℝ² (2D Euclidean plane).

### Regularized field
- Configuration space: `FinLatticeField 2 N = FinLatticeSites 2 N → ℝ`
- Field at a point: `φ(x)` — function evaluation on lattice sites
- No sorry needed: lattice configurations ARE functions

### Interaction
```
V_a(φ) = a² Σ_{x ∈ (ℤ/Nℤ)²} :P(φ(x)):_{c_a}
```
where `c_a = wickConstant 2 N a mass`. Fully concrete, 0 axioms.
Bounded below: proved.

### Continuum limit
1. Embed lattice into continuum via Riemann sum: `ι_a(φ)(f) = a² Σ_x φ(x) f(ax)`
2. Tightness of `{(ι_a)_* μ_a}_{a→0}` (axiom — Nelson bounds + Mitoma)
3. Prokhorov extracts weakly convergent subsequence
4. Limit lives on `Configuration(SchwartzMap(ℝ²) ℝ)`

### OS axiom strategy
| Axiom | Status | Method |
|-------|--------|--------|
| OS0 (Analyticity) | axiom | Vitali convergence for analytic functions under weak limits |
| OS1 (Regularity) | proved | Uniform moment bounds transfer to limit |
| OS2 (Euclidean invariance) | proved | Translation: lattice symmetry. Rotation: Ward identity + superrenormalizability |
| OS3 (Reflection positivity) | proved | Transfer matrix → lattice RP → closed under weak limits |
| OS4 (Clustering/mass gap) | proved | Perron-Frobenius spectral gap for 1D transfer matrix |

### Spacetime dependence
- OS2 rotation: Ward identity anomaly bound uses d=2 superrenormalizability
- OS3: transfer matrix decomposition uses d=2 (1D spatial slices)
- OS4: Jentzsch/Perron-Frobenius on 1D transfer matrix, d=2 specific

### Status: 25 axioms, 0 sorries
Main theorem: `pphi2_exists`

---

## Route B: Lattice → Torus T²_L

**Purpose:** Finite-volume warm-up for Route A.

**Spacetime:** T²_L = (ℝ/Lℤ)² (2D torus of side length L).

### Regularized field
Same as Route A: `FinLatticeField 2 N`, field is `φ(x)`.

### Interaction
Same lattice interaction as Route A, with `a = L/N`.

### Interacting measure
Pushforward of Route A lattice measure under torus embedding:
```lean
torusInteractingMeasure N P mass = Measure.map (torusEmbedLift L N) (interactingLatticeMeasure ...)
```
No new field evaluation — inherits everything from the lattice.

### Continuum limit
Lattice spacing `a = L/N → 0` as `N → ∞`. Same Prokhorov strategy as Route A.
Gaussian limit identified with torus Green's function.

### OS axiom strategy
| Axiom | Status | Method |
|-------|--------|--------|
| OS0 (Analyticity) | axiom | Same as Route A |
| OS1 (Regularity) | proved | Moment bounds |
| OS2 (Translation) | proved | Manifest from lattice periodicity |
| OS3 (RP) | axiom | Inherited from lattice |

### Spacetime dependence
- Finite volume: no IR divergences, simpler analysis
- Discrete spatial spectrum (periodic boundary)
- No rotation invariance needed

### Status: 7 axioms, 0 sorries
Main theorem: `torusInteractingLimit_exists`
Note: `torus_interacting_tightness` converted from axiom to theorem via
`nelson_exponential_estimate` + Mitoma-Chebyshev + density transfer + hypercontractivity.

---

## Route C: Direct on Cylinder S¹_L × ℝ

**Purpose:** Direct Nelson/Simon construction, natural for OS reconstruction.

**Spacetime:** S¹_L × ℝ (circle × real line).

### Regularized field
- Configuration space: `Configuration(CylinderTestFunction L)` where
  `CylinderTestFunction L = C∞(S¹_L) ⊗̂ 𝓢(ℝ)` (distributions, not functions)
- Field at a point:
  ```
  φ_Λ(θ,t)(ω) = Σ_{n=0}^{2Λ} fourierBasisFun(n)(θ) · X_n(t)(ω)
  ```
  where `X_n(t)` = `cylinderOUProcessEval` (**sorry** — isonormal Gaussian extension)
- Wick constant: `cylinderWickConstant L mass Λ = Σ_{n=0}^{2Λ} 1/(2ω_n L)`

### The sorry
`cylinderOUProcessEval` is sorry'd because evaluating the OU process at time t
requires extending ω from nuclear test functions to L²(ℝ). The resolvent kernel
`exp(-ω_n|t-s|)/√(2ω_n)` is L² but not Schwartz.

**Alternative (not yet implemented):** Work with function-valued configurations
for the regularized theory. With UV cutoff Λ, the field is determined by (2Λ+1)
continuous paths — one per spatial mode. On this space, field evaluation is
trivial (function evaluation), eliminating the sorry.

### Interaction
Two cutoffs — spatial UV and temporal IR:
```
V_{Λ,T}(ω) = ∫₀ᴸ ∫₋ᵀᵀ :P(φ_Λ(θ,t)(ω)):_{c_Λ} dt dθ
```
Bounded below: proved.

### Continuum limit
Two-step (no lattice):
1. **UV limit** (Λ→∞): `cylinderUVLimitMeasure` = weak-lim of (1/Z) exp(-V_{Λ,T}) dμ_free
2. **IR limit** (T→∞): `cylinderMeasure` = weak-lim of UV-limit measures
Both use hypercontractivity for uniform bounds → tightness → Prokhorov.

### OS axiom strategy
| Axiom | Status | Method |
|-------|--------|--------|
| OS0 (Analyticity) | axiom | Exponential moment bounds through both limits |
| OS1 (Regularity) | axiom | Density transfer from Gaussian |
| OS2 (Spatial) | axiom | V invariant under θ-translation on S¹_L |
| OS2 (Time translation) | axiom | Broken at finite T, restored in T→∞ limit |
| OS2 (Time reflection) | axiom | V and domain [-T,T] are Θ-symmetric |
| OS3 (RP) | axiom | Lattice RP preserved under weak limits (RP infrastructure proved: `cylinderMatrixRP_of_weakLimit`) |

### Spacetime dependence
- Spatial S¹_L: Fourier decomposition, clean mode-by-mode analysis
- Temporal ℝ: natural positive-time half-space for OS reconstruction
- Time translation invariance requires careful IR limit argument
- No rotation invariance (not a symmetry of S¹_L × ℝ)

### Key difference from Routes A/B
Routes A and B: lattice → configurations are functions → field at a point is trivial.
Route C: starts in continuum → configurations are distributions → field at a point needs isonormal extension (sorry).

### Status: 23 axioms + 1 sorry
Main theorem: `cylinderInteracting_satisfies_OS`

---

## Comparison

| | Route A (ℝ²) | Route B (T²) | Route C (S¹×ℝ) |
|--|--|--|--|
| **Purpose** | Main theorem | Warm-up | OS reconstruction |
| **Configurations** | Functions (lattice) | Functions (lattice) | Distributions (continuum) |
| **Field at a point** | `φ(x)` (trivial) | `φ(x)` (trivial) | sorry (isonormal) |
| **Limit type** | a → 0 (single) | N → ∞ (single) | Λ→∞ then T→∞ (two-step) |
| **OS proved** | OS1–OS4 | OS1–OS2 | none (all axiom'd) |
| **OS axiom'd** | OS0 | OS0, OS3 | OS0–OS3 |
| **Axioms** | 25 | 7 | 23 + 1 sorry |

### Upstream (gaussian-field repo): 13 axioms
Key axioms: `cylinderMassOperator`, `cylinderGreen_pos`,
`cylinderMassOperator_equivariant_of_heat_comm`, resolvent multiplier properties.

### Grand total: 60 axioms + 1 sorry (pphi2) + 13 axioms (gaussian-field)
