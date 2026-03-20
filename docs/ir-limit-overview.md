# Route B' IR Limit: Overview and Remaining Work

**Updated**: 2026-03-20

## Architecture

Route B' constructs the P(φ)₂ QFT on the cylinder S¹_{Ls} × ℝ in two steps:

```
Step 1 (DONE): UV limit on asymmetric torus T_{Lt,Ls}
    Lattice (ℤ/Nℤ)² → N→∞ → Continuum torus T_{Lt,Ls}
    AsymTorusOS.lean: 0 axioms, 0 sorries
    OS0–OS2 fully proved for every finite Lt, Ls

Step 2 (IN PROGRESS): IR limit Lt → ∞
    Family {μ_{Lt}} on T_{Lt,Ls} → Lt→∞ → Limit ν on S¹_{Ls} × ℝ
    IRLimit/: 5 axioms, 0 sorries
    OS0, OS3 axiomatized; OS2 proved via weak limit
```

## Test Function Spaces

```
CylinderTestFunction Ls = C∞(S¹_{Ls}) ⊗̂ 𝓢(ℝ)    [spatial × temporal]
AsymTorusTestFunction Lt Ls = C∞(S¹_{Lt}) ⊗̂ C∞(S¹_{Ls})  [temporal × spatial]
```

The embedding `cylinderToTorusEmbed Lt Ls` periodizes the Schwartz temporal
factor to period Lt, then swaps to match conventions:

```
CylinderTestFunction Ls  ──[id ⊗ periodize_Lt]──>  C∞(S¹_{Ls}) ⊗̂ C∞(S¹_{Lt})
                          ──[swap]──>  AsymTorusTestFunction Lt Ls
```

## File Structure

| File | Content | Axioms | Status |
|------|---------|--------|--------|
| `Periodization.lean` | Re-exports `periodizeCLM` from gaussian-field | 0 | ✓ |
| `CylinderEmbedding.lean` | Embedding def, pullback, intertwining | 0 | **Fully proved** |
| `GreenFunctionComparison.lean` | Uniform 2nd moment bound | 1 | Axiom |
| `UniformExponentialMoment.lean` | Uniform exponential moment | 1 | Axiom |
| `IRTightness.lean` | Prokhorov extraction | 1 | Axiom |
| `CylinderOS.lean` | OS0, OS2, OS3 for the limit | 2 | OS2 proved, OS0+OS3 axioms |

## What's Proved

### Definitions (all constructive, no axioms)
- `cylinderToTorusEmbed` — the embedding CLM (def in both pphi2 and gaussian-field)
- `cylinderPullback` — pullback on configurations: `ω_cyl(f) = ω_torus(embed f)`
- `cylinderPullbackMeasure` — pushforward measure
- `cylinderPullback_eval` — evaluation formula (simp lemma)

### Theorems
- **`cylinderPullback_continuous`** — WeakDual continuity via `eval_continuous`
- **`cylinderToTorusEmbed_comp_timeTranslation`** — intertwining with time shift
  (via NTP pure tensor density + `periodizeCLM_comp_schwartzTranslation`)
- **`cylinderToTorusEmbed_comp_timeReflection`** — intertwining with time reflection
  (via NTP pure tensor density + `periodizeCLM_comp_schwartzReflection`)
- **`cylinderPullback_timeTranslation_invariant`** — pullback is time-translation invariant
  (via `integral_map` + intertwining + torus translation invariance)
- **`cylinderPullback_timeReflection_invariant`** — pullback is time-reflection invariant
  (via `integral_map` + intertwining + torus reflection invariance)
- **OS2 in `routeBPrime_cylinder_OS`** — time reflection of the IR limit
  (via `tendsto_nhds_unique` + characteristic functional convergence)

### Key technique: NTP pure tensor density
The intertwining proofs use `cylinderToTorus_clm_ext_of_pure`: two CLMs on an NTP
that agree on all pure tensors are equal. This reduces CLM equality to:
1. `rapidDecay_expansion` — expand input via DM basis
2. `basisVec_eq_pure` — each basis vector is a pure tensor
3. Check on pure tensors using `mapCLM_general_pure`, `swapCLM_pure`

## Remaining Axioms (5)

### 1. `cylinderIR_uniform_second_moment`
**Statement**: `∫ (ωf)² d(pullback μ) ≤ C · q(f)²` uniformly in Lt ≥ 1.

**Proof route**:
1. Pullback identity: `∫ (ωf)² dν_Lt = ∫ (ω(embed f))² dμ`
2. OS1 regularity of μ → `∫ (ωg)² dμ ≤ C₁ · q₁(g)²`
3. Method of images: `q₁(embed f) ≤ C₂ · q₂(f)` (from `torusGreen_uniform_bound`)

**Blocked on**: The chain requires connecting the second moment to the Green's
function via the covariance operator, which needs the spectral decomposition
identity. The Green function uniform bound (`torusGreen_uniform_bound`) is
an axiom in gaussian-field.

**Estimated effort**: ~200 lines once the uniform bound is available.

### 2. `cylinderIR_uniform_exponential_moment`
**Statement**: `∫ exp(|ωf|) d(pullback μ) ≤ K · exp(C · q(f)²)` uniformly in Lt ≥ 1.

**Proof route**: From `AsymSatisfiesTorusOS.os1` (torus exponential moment bound)
applied to `g = embed(f)`, combined with method of images bound.

**Depends on**: Axiom 1 (second moment → exponential moment via Nelson bound).

**Estimated effort**: ~100 lines.

### 3. `cylinderIRLimit_exists`
**Statement**: Weakly convergent subsequence with characteristic functional convergence.

**Proof route**:
1. Uniform second moments (Axiom 1) → Mitoma-Chebyshev tightness
2. `configuration_tight_of_uniform_second_moments` (gaussian-field, proved)
3. Prokhorov extraction (Polish space, proved for torus)

**Depends on**: Axiom 1. Also needs `CylinderTestFunction Ls` to be Polish
(or use the Lévy continuity theorem on nuclear spaces).

**Estimated effort**: ~150 lines following `AsymTorusInteractingLimit` template.

### 4. `cylinderIR_os0` (OS0: Analyticity)
**Statement**: Generating functional is entire analytic on ℂⁿ.

**Proof route**: Uniform exponential moments (Axiom 2) → locally uniform
boundedness → Vitali/Montel → analyticity of the limit.

**Depends on**: Axiom 2 + Axiom 3 (need both the bounds and the convergence).

**Estimated effort**: ~200 lines. Requires complex analysis (Vitali/Montel).

### 5. `cylinderIR_os3` (OS3: Reflection Positivity)
**Statement**: RP quadratic form is nonneg for positive-time test functions.

**Proof route**:
1. Restrict to `f ∈ C_c^∞((0,R) × S¹)` (compactly supported in positive time)
2. For Lt > 2R, `embed f` has no wrap-around → fits in positive half of torus
3. Torus RP applies exactly → ∫ F·(ΘF) dμ_Lt ≥ 0
4. Pass through weak limit (RP closed under weak limits, proved)
5. Extend by density of `C_c^∞((0,∞) × S¹)` in positive Schwartz space

**Depends on**: Axiom 3 (weak convergence) + torus RP (proved in AsymTorusOS).

**Estimated effort**: ~200 lines. The wrap-around argument uses
`periodizeCLM_eq_on_large_period` (proved in gaussian-field).

## Dependency Graph

```
cylinderIR_uniform_second_moment (Axiom 1)
    ↓
cylinderIR_uniform_exponential_moment (Axiom 2)
    ↓
cylinderIRLimit_exists (Axiom 3) ← also depends on Axiom 1
    ↓
cylinderIR_os0 (Axiom 4) ← also depends on Axiom 2
cylinderIR_os3 (Axiom 5) ← depends on Axiom 3 + torus RP
```

The critical path is Axiom 1 → Axiom 2 → Axiom 3 → Axioms 4,5.

## Upstream Dependencies (gaussian-field)

The IR limit relies on these gaussian-field components:

| Component | Axioms | Status |
|-----------|--------|--------|
| `Cylinder/Basic.lean` | 0 | CylinderTestFunction type (def) |
| `Cylinder/Symmetry.lean` | 0 | Translation, reflection CLMs (defs + theorems) |
| `Cylinder/PositiveTime.lean` | 0 | Positive-time submodule (def + theorems) |
| `Cylinder/GreenFunction.lean` | 3 | Mass operator, Green's function, heat equivariance |
| `Cylinder/ReflectionPositivity.lean` | 3 | Laplace embedding, OS3 for free field |
| `Cylinder/MethodOfImages.lean` | 1 | `torusGreen_uniform_bound` |
| `Cylinder/FourierMultiplier.lean` | 3 | Fourier multiplier properties |
| `SchwartzNuclear/Periodization.lean` | 2 | `periodizeCLM` + pointwise formula |
| `Nuclear/GeneralMapCLM.lean` | 2 | NTP functor for general CLMs |

Total gaussian-field axioms for IR limit: 14 (these support the cylinder + method of images).

## What Would Close the IR Limit

To prove all 5 remaining IR limit axioms, the main missing pieces are:

1. **Method of images integration**: Connecting `torusGreen_uniform_bound` to the
   second moment bound via the covariance operator. This is the spectral
   decomposition → Green function → variance chain.

2. **Exponential moment transfer**: Pulling the Nelson/Fröhlich bound through
   the embedding. This uses the OS1 regularity of the torus measure.

3. **Polish space for cylinder configurations**: Either prove
   `PolishSpace (Configuration (CylinderTestFunction Ls))` or use Lévy
   continuity on nuclear spaces for Prokhorov extraction.

4. **Complex analysis for OS0**: Vitali/Montel theorem for sequences of
   analytic functions with uniform bounds. May need Mathlib complex analysis.

5. **Density argument for OS3**: Showing `C_c^∞((0,∞) × S¹)` is dense in the
   positive-time submodule, and using `periodizeCLM_eq_on_large_period` for
   the no-wrap-around argument.

## Comparison with Other Routes

| Route | Geometry | OS axioms proved | Axioms | Sorries |
|-------|----------|------------------|--------|---------|
| B (torus) | T²_L | OS0–OS2 | ~1 | ~1 |
| B' UV (asym torus) | T_{Lt,Ls} | OS0–OS2 | 0 | 0 |
| B' IR (cylinder) | S¹_{Ls} × ℝ | OS2 | 5 | 0 |
| C (cylinder direct) | S¹_L × ℝ | (planned) | 21 (in future/) | 1 |

Route B' is the most developed cylinder route. Compared to Route C (direct
cylinder construction), it reuses all of Route B's UV limit infrastructure
and adds only the IR limit step.

## Next Steps

1. **Prove Axiom 1** (`cylinderIR_uniform_second_moment`): The most impactful
   single step. Requires connecting the pullback integral to the Green
   function via the covariance operator.

2. **Prove Axiom 3** (`cylinderIRLimit_exists`): Once Axiom 1 is available,
   this follows the `AsymTorusInteractingLimit` template closely.

3. **Prove Axiom 5** (`cylinderIR_os3`): The wrap-around argument +
   density is the most novel part of the IR limit construction.

4. **Prove Axioms 2,4**: These are intermediate steps (exponential moments
   for OS0 analyticity) that follow from existing torus bounds.
