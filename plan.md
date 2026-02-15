# Plan: Formal Construction of P(Φ)₂ in Lean 4

## Goal

Formalize the construction of the P(Φ)₂ Euclidean quantum field theory
on the cylinder ℝ × S¹_L and verify partial Osterwalder-Schrader axioms,
following Duch-Dybalski-Jahandideh (arXiv:2311.04137).

The main theorem (DDJ Theorem 1.1, adapted to cylinders):

> For each L > 0, the P(Φ)₂ measure μ_L on D'(ℝ × S¹_L) exists as the
> UV limit of regularized measures. The family {μ_L} is tight and every
> accumulation point μ on S'(ℝ²) satisfies:
> - (OS1) Euclidean invariance
> - (OS3) Reflection positivity
> - (OS5/Regularity) ∃ ball B ⊂ S(ℝ²) s.t. ∀f ∈ B, ∫ exp(φ(f)ⁿ) dμ ≤ 2

Clustering (OS4) is known only for small coupling and is not part of DDJ.

---

## Primary Reference

**Duch, Dybalski, Jahandideh** (2311.04137):
*Stochastic quantization of two-dimensional P(Φ) Quantum Field Theory*

Located at: `refs/duch-dybalski-jahandideh-2311.04137/`

### Supplementary References

- Barashkov-Gubinelli (1805.10814): Variational method for Φ⁴₃
- Gubinelli-Hofmanova (1810.01700): PDE construction of Φ⁴₃
- Barashkov-Gubinelli (2112.05562): Infinite volume φ⁴₂ tightness
- Gubinelli (2025): GSSI lecture notes on fractional Φ⁴₃

---

## Approach: Cylinders Instead of Spheres

DDJ works on spheres S_R → ℝ² via stereographic projection. We work on
cylinders ℝ × S¹_L → ℝ² via the L → ∞ limit instead. The cylinder approach:

- **Preserves time direction:** ℝ factor is continuous time, giving natural
  time reflection and positive-time support without stereographic subtleties.
- **Fourier mode decomposition:** S(ℝ × S¹_L) ≅ {ℤ-indexed Schwartz families
  with rapid decay}, making test functions concrete.
- **Fits QFTFramework:** The cylinder has the same structure as OSforGFF
  (spacetime, test functions, field configurations, symmetry group).
- **Trade-off:** We lose the SO(3) ≅ E(2) trick for Euclidean invariance.
  Translation invariance must be proved via the L → ∞ limit directly.

---

## Dependencies

- **OSforGFF-dimensions** (`OSforGFF/`): QFTFramework structure, OS axiom
  definitions, nuclear space class, Minlos theorem, positive definiteness.
- **Mathlib**: Schwartz space, seminorms, AddCircle, measure theory, weak dual.
- **aqft2** (sibling project): Schwartz function infrastructure, Hermite
  functions, nuclear factorization. Not a build dependency but shares patterns.

---

## Current State

### File Structure and Status

```
Pphi2/
  Basic.lean                          338 lines, 46 sorrys  ← ACTIVE
  Polynomial.lean                      41 lines,  3 sorrys
  OSAxioms.lean                        28 lines,  0 sorrys  (structure definition only)
  Main.lean                            52 lines,  3 sorrys

  GaussianCylinder/
    Covariance.lean                    70 lines,  0 sorrys  (9 axioms)

  MeasureCylinder/
    Regularized.lean                   36 lines,  0 sorrys  (3 axioms)
    UVLimit.lean                       24 lines,  0 sorrys  (3 axioms)

  StochasticQuant/
    DaPratoDebussche.lean              79 lines,  0 sorrys  (7 axioms)

  StochasticEst/
    InfiniteVolumeBound.lean           26 lines,  0 sorrys  (2 axioms)

  Energy/
    EnergyEstimate.lean                32 lines,  0 sorrys  (4 axioms)

  FunctionSpaces/
    WeightedLp.lean                    40 lines,  2 sorrys
    Embedding.lean                     31 lines,  0 sorrys  (4 axioms)

  InfiniteVolume/
    Tightness.lean                     68 lines,  0 sorrys  (3 axioms)

  Integrability/
    Regularity.lean                    51 lines,  2 sorrys

  ReflectionPositivity/
    RPPlane.lean                       74 lines,  1 sorry

  EuclideanInvariance/
    Invariance.lean                    54 lines,  1 sorry
```

**Summary:** 16 files, ~1065 lines, 58 sorrys, ~35 axioms. Most downstream
files are axiom signatures with the proof architecture sketched. The active
development front is `Basic.lean`.

### What's Concrete in Basic.lean

- `SpaceTimeCyl d L = ℝ × AddCircle L`
- `TestFunctionCyl d L`: structure with `fourierMode : ℤ → SchwartzMap ℝ ℂ`,
  `rapidDecay`, and `reality` condition
- `TestFunctionCylℂ d L`: same without reality condition
- `FieldConfigurationCyl d L = WeakDual ℝ (TestFunctionCyl d L)`
- `QFTFramework.cylinder`: all 8 operational fields filled with concrete
  definitions (sorry'd proofs, concrete type signatures)
- `realGenFunctionalCyl`: Z[J] = ∫ exp(i⟨ω,J⟩) dμ — fully concrete
- `complexGenFunctionalCyl`: built on `complexPairingCyl` (sorry'd)
- `positiveTimeSubmoduleCyl`: carrier = {f | ∀n, tsupport(fₙ) ⊆ Ioi 0}
- `timeReflectionCyl`, `translateTestFunCyl`: type signatures concrete, bodies sorry'd

### What's Still Axiomatized

- `SymmetryGroupCyl d L`: axiom (blocks `symmetryActionCyl`)
- `laplacianCylinder`, `freeCovariance`: axiom CLMs
- `counterterm`, `counterterm_bound`: axiom
- All topology instances on `TestFunctionCyl`: sorry

---

## Proof Architecture (DDJ, Adapted to Cylinders)

### Section 2: UV Limit on the Cylinder

Replace S_R with ℝ × S¹_L. The Laplacian Δ_L has eigenvalues
-(k² + (2πn/L)²) in the Fourier representation.

- G_L = (1 - Δ_L)⁻¹: free covariance (axiom `freeCovariance`)
- K_{L,N}: UV regularization operator
- ν_{L,N}: Gaussian measure with covariance G_{L,N} = K_{L,N} G_L K_{L,N}
- c_{L,N}: counterterm (Wick ordering constant)
- μ_{L,N}: regularized P(Φ)₂ measure

**Files:** `GaussianCylinder/Covariance.lean`, `MeasureCylinder/Regularized.lean`,
`MeasureCylinder/UVLimit.lean`

### Section 3: Stochastic Quantization

Da Prato-Debussche decomposition Φ = Ψ + Z where Z is the OU process
(Gaussian) and Ψ satisfies a PDE with non-singular nonlinearity.

**File:** `StochasticQuant/DaPratoDebussche.lean`

### Section 5: Energy Estimate

The core a priori bound, uniform in L and N. Controls ‖Ψ‖ by free-field
stochastic terms.

**File:** `Energy/EnergyEstimate.lean`

### Section 6: Tightness and Infinite Volume

Uniform moment bounds → tightness → Prokhorov → subsequential convergence.

**Files:** `InfiniteVolume/Tightness.lean`, `StochasticEst/InfiniteVolumeBound.lean`

### Section 7: Integrability / OS Regularity

Variational bound (Barashkov) + tightness → ∫ exp(φ(f)ⁿ) dμ ≤ 2.

**File:** `Integrability/Regularity.lean`

### Section 8: Reflection Positivity

Time reflection Θ: t ↦ -t on the cylinder. Free field is RP; interaction
preserves RP by half-space factorization.

**File:** `ReflectionPositivity/RPPlane.lean`

### Section 9: Euclidean Invariance

Translation invariance via L → ∞ limit. Rotation invariance from the
circle symmetry.

**File:** `EuclideanInvariance/Invariance.lean`

---

## Development Phases

### Phase 0: Schwartz Infrastructure (CURRENT)

Fill sorrys in `Basic.lean` — the algebraic and analytic foundations.

**Phase 0a: Algebraic proofs** (straightforward, ~30 sorrys)
- [ ] `ext` lemma for `TestFunctionCyl` and `TestFunctionCylℂ`
- [ ] `AddCommGroup` laws (add_assoc, zero_add, add_zero, add_comm, neg_add_cancel)
- [ ] `Module ℝ` laws (one_smul, mul_smul, smul_zero, smul_add, add_smul, zero_smul)
- [ ] Same for `TestFunctionCylℂ` with `Module ℂ`
- [ ] Rapid decay closure: add, neg, zero, smul
- [ ] Reality condition closure: add, neg, zero, smul

All ingredients are in Mathlib: `map_add_le_add`, `map_neg_eq_map`, `map_zero`,
`map_smul_eq_mul` for seminorms; `star_add`, `star_neg`, `star_zero`,
`Complex.conj_ofReal` for reality. See `refs/schwartz-map-lemmas.md`.

**Phase 0b: Submodule and operations** (~6 sorrys)
- [ ] `positiveTimeSubmoduleCyl`: zero_mem' (tsupport_zero), add_mem', smul_mem'
- [ ] `timeReflectionCyl`: compose modes with negation via `SchwartzMap.compCLMOfContinuousLinearEquiv`
- [ ] `complexPairingCyl`: Re/Im decomposition of complex test functions

**Phase 0c: Leave as sorry/axiom**
- Topology instances (requires defining Fréchet topology on mode families)
- `symmetryActionCyl` (blocked on axiomatized `SymmetryGroupCyl`)
- `translateTestFunCyl` (translation is affine, needs custom argument)
- `timeTranslationDistCyl` (depends on translation)
- `NuclearSpace` (textbook result, axiomatized as in aqft2)

### Phase 1: Gaussian Theory on the Cylinder

- [ ] Make `freeCovariance` concrete (mode-by-mode: multiply by 1/(1 + k² + (2πn/L)²))
- [ ] Counterterm c_{L,N} = trace of regularized covariance
- [ ] Gaussian measure ν_{L,N} via Minlos theorem (from OSforGFF)
- [ ] Wick ordering in Fourier representation
- [ ] Nelson hypercontractivity (axiomatize, as in aqft2)

### Phase 2: Stochastic Quantization

- [ ] OU process Z_{L,N}(t) — axiomatize cylindrical Wiener process
- [ ] Da Prato-Debussche remainder Ψ = Φ - Z
- [ ] PDE for Ψ (non-singular nonlinearity)
- [ ] Stationarity: Law(Φ(t)) = μ_{L,N}

### Phase 3: Core Estimates

- [ ] Energy estimate (Prop 5.1) — the hardest analytical part
- [ ] Stochastic moment bounds uniform in L, N
- [ ] Cross-term estimates (Lemma A.5 via Sobolev interpolation)
- [ ] Function space infrastructure: weighted Bessel potential spaces, embeddings

### Phase 4: Limit and Axioms

- [ ] Tightness (Prop 6.1) from energy estimate
- [ ] UV limit μ_L = lim_N μ_{L,N} via Vitali
- [ ] Infinite volume: tightness of {μ_L}, Prokhorov
- [ ] OS regularity (Prop 7.1) via variational bound
- [ ] Reflection positivity (Sec 8)
- [ ] Euclidean invariance (Sec 9)

### Phase 5: Assembly

- [ ] `Main.lean`: combine all OS axioms into `SatisfiesDDJ_OS_generic`

---

## Relationship to Sibling Projects

### aqft2 (GFF on ℝ^d)

Proves all 5 OS axioms for the free Gaussian field. Shares:
- Schwartz function infrastructure (`FunctionalAnalysis.lean`: 60+ lemmas)
- Nuclear space framework and Hermite expansion
- OS axiom definitions and generating functional patterns
- Minlos theorem application pattern

Does NOT share: interacting theory, stochastic quantization, cylinder geometry.

### OSforGFF-dimensions

Provides the `QFTFramework` structure that pphi2 instantiates. Also provides:
- OS axiom type classes (`OS0`–`OS4`)
- `NuclearSpace` class (if/when upstreamed from aqft2)
- `WeakDual` field configuration pattern

### Coordination needed

- `NuclearSpace`: currently defined locally in pphi2 as a stub class.
  Should be replaced with the real definition from OSforGFF once available.
- Schwartz lemmas proved in aqft2 could be factored into a shared library.
- `QFTFramework` may evolve toward the `FieldSpace` hierarchy
  (see `field-space-brainstorming.md`) but not yet.

---

## Key Difficulties

### Hard (require substantial new Lean work)
1. **Topology on TestFunctionCyl:** The Fréchet topology on ℤ-indexed Schwartz
   families is not in Mathlib. Could use the product topology on ℤ → 𝓢(ℝ,ℂ)
   restricted to the rapid-decay subspace, but the restriction topology needs care.
2. **Energy estimate (Prop 5.1):** Many intermediate bounds, integration by parts
   with weights. The core technical challenge of the whole formalization.
3. **Cylindrical Wiener process:** No Lean formalization exists. Must axiomatize.
4. **Sobolev embeddings for weighted spaces:** Not in Mathlib.

### Medium (require careful but routine Lean work)
5. **Time reflection via compCLM:** Composition with negation. The CLM exists
   in Mathlib; need to verify rapid decay and reality are preserved.
6. **Complex pairing:** Decompose SchwartzMap ℝ ℂ into Re/Im parts. Requires
   showing `Complex.reCLM ∘ f` and `Complex.imCLM ∘ f` are Schwartz.
7. **Translation on the cylinder:** Affine map, not covered by `compCLMOfContinuousLinearEquiv`.

### Likely axioms needed long-term
- Spectral theory of Δ_L on the cylinder (eigenvalue decomposition)
- Cylindrical Wiener process existence and properties
- Nelson hypercontractivity / Gross log-Sobolev inequality
- Sobolev embedding theorems for weighted Bessel spaces
- Prokhorov's theorem (partial in Mathlib)

---

## File Index

| File | Role | Status |
|------|------|--------|
| `Basic.lean` | Core types, QFTFramework instance | 46 sorrys, active |
| `Polynomial.lean` | Interaction polynomial P(τ) | 3 sorrys |
| `OSAxioms.lean` | `SatisfiesDDJ_OS_generic` structure | complete |
| `Main.lean` | Main theorem assembly | 3 sorrys |
| `GaussianCylinder/Covariance.lean` | Free covariance, Gaussian measure | axioms |
| `MeasureCylinder/Regularized.lean` | Regularized P(Φ)₂ measure | axioms |
| `MeasureCylinder/UVLimit.lean` | UV limit N → ∞ | axioms |
| `StochasticQuant/DaPratoDebussche.lean` | Da Prato-Debussche decomposition | axioms |
| `StochasticEst/InfiniteVolumeBound.lean` | Free field moment bounds | axioms |
| `Energy/EnergyEstimate.lean` | A priori energy bound | axioms |
| `FunctionSpaces/WeightedLp.lean` | Weighted Lp, Bessel spaces | 2 sorrys |
| `FunctionSpaces/Embedding.lean` | Sobolev embeddings | axioms |
| `InfiniteVolume/Tightness.lean` | Tightness, Prokhorov | axioms |
| `Integrability/Regularity.lean` | OS regularity bound | 2 sorrys |
| `ReflectionPositivity/RPPlane.lean` | Reflection positivity | 1 sorry |
| `EuclideanInvariance/Invariance.lean` | Euclidean invariance | 1 sorry |

| Supporting doc | Content |
|---------------|---------|
| `refs/schwartz-map-lemmas.md` | Mathlib Schwartz API inventory |
| `field-space-brainstorming.md` | FieldSpace architecture analysis |
| `docs/os_axioms_lattice_plan.md` | Lattice OS axiom plan |

---

## Immediate Next Steps

1. **Phase 0a:** Prove `ext` lemma and algebraic instances in `Basic.lean`
2. **Phase 0b:** Prove `positiveTimeSubmoduleCyl` closure properties
3. Coordinate with aqft2 on shared Schwartz lemma needs
4. Make `freeCovariance` concrete (mode-by-mode multiplication)
