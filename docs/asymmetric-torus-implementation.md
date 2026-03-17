# Asymmetric Torus Implementation Plan

## Goal

Generalize the symmetric torus T²_L = (ℝ/Lℤ)² infrastructure to the
asymmetric torus T_{L,W} = (ℝ/Lℤ) × (ℝ/Wℤ) with independent periods
L (time) and W (space). This enables Route B' (cylinder via L → ∞).

## What Changes in gaussian-field

### Already generic (no changes needed)

The nuclear tensor product infrastructure is ALREADY parametric in the
two factor spaces:

- `NuclearTensorProduct E₁ E₂` — takes any two DyninMityaginSpaces
- `evalCLM`, `evalCLM_comp_swapCLM`, `evalCLM_comp_mapCLM` — generic
- `nuclearTensorProduct_mapCLM`, `nuclearTensorProduct_swapCLM` — generic
- `basisVec_eq_pure`, `mapImage_seminorm_bound` — generic
- `greenFunctionBilinear` — uses `HasLaplacianEigenvalues` typeclass

So `AsymTorusTestFunction L W := NuclearTensorProduct (SmoothMap_Circle L ℝ) (SmoothMap_Circle W ℝ)`
works immediately with all existing NTP infrastructure.

### Needs generalization (minor)

1. **`Torus/Evaluation.lean`**: `evalTorusAtSite` currently uses
   `circleRestriction L N` for BOTH factors. For asymmetric torus:
   - Factor 1: `circleRestriction L N_L` (time, spacing L/N_L)
   - Factor 2: `circleRestriction W N_W` (space, spacing W/N_W)
   - Change: parameterize by (L, N_L) and (W, N_W) independently

2. **`Torus/Symmetry.lean`**: `torusTranslation L v` uses
   `circleTranslation L v.1` and `circleTranslation L v.2` with same L.
   - Change: `circleTranslation L v.1` and `circleTranslation W v.2`

3. **`HeatKernel/GreenInvariance.lean`**: Green's function invariance proofs
   use `SmoothMap_Circle L ℝ` for both factors.
   - Change: allow different circle parameters

4. **`Torus/Restriction.lean`**: `circleSpacing L N = L/N`. For asymmetric:
   need two spacings `a_L = L/N_L` and `a_W = W/N_W`.

### Needs new definitions

5. **`AsymmetricTorus.lean`** (new file):
   ```lean
   def AsymTorusTestFunction (L W : ℝ) [Fact (0 < L)] [Fact (0 < W)] :=
     NuclearTensorProduct (SmoothMap_Circle L ℝ) (SmoothMap_Circle W ℝ)
   ```
   Plus: asymmetric lattice sites `(ℤ/N_L ℤ) × (ℤ/N_W ℤ)`, embedding,
   Green's function, propagator convergence.

## What Changes in pphi2

### Route B proofs that generalize directly

ALL of `TorusInteractingOS.lean` uses only:
- NTP generic operations (evalCLM, mapCLM, pure, basisVec)
- `evalTorusAtSite` (needs parameter generalization)
- `latticeTestFn`, `torusEmbedLift` (needs parameter generalization)
- `latticeGaussianMeasure`, `interactingLatticeMeasure` (already generic in d, N)
- `circleSpacing` (needs two versions)

The proof STRUCTURE is completely generic. Only the TYPE SIGNATURES change
(replacing `L` with `(L, W)` in appropriate places).

### New infrastructure for L → ∞

1. **Embedding maps**: For L' > L, embed T_{L,W} test functions into
   T_{L',W} test functions (extend by zero or periodize).

2. **Tightness for L → ∞**: Uniform-in-L bounds on moments.
   Key: G_{L,W}(f,f) ≤ G_W(f,f) for compactly supported f
   (the cylinder Green's function dominates the torus one).

3. **Weak convergence**: Prokhorov extraction for L → ∞.

4. **OS axiom transfer**: Same weak limit arguments as Route B.

## Estimated Effort

| Task | Difficulty | Lines |
|------|-----------|-------|
| AsymTorusTestFunction definition | Easy | ~50 |
| Generalize evalTorusAtSite | Easy | ~20 (parameter changes) |
| Generalize torusTranslation | Easy | ~10 |
| Generalize TorusInteractingOS | Medium | ~200 (copy + adapt types) |
| L → ∞ embedding maps | Medium | ~100 |
| L → ∞ tightness | Medium | ~150 |
| L → ∞ weak convergence | Easy | ~50 (same as N → ∞) |
| OS3 from transfer matrix | Hard | ~300 (adapt Route C) |

Total: ~900 lines new, ~200 lines modified.

## Order of Implementation

1. Define `AsymTorusTestFunction L W` (trivial, just a type alias)
2. Generalize `evalTorusAtSite` to asymmetric lattice
3. Generalize `torusEmbedLift` and `latticeTestFn`
4. Copy Route B proofs with asymmetric types
5. Implement L → ∞ embedding and tightness
6. Prove OS0–OS2 for the cylinder limit
7. Adapt OS3 from Route C's transfer matrix

Steps 1-4 are mechanical. Steps 5-6 are the main new mathematics.
Step 7 connects to existing infrastructure.
