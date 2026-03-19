# Cylinder IR Limit: Implementation Plan

## Goal

Take the family of asymmetric torus measures `{μ_{P,Lt,Ls}}` (from the
proved UV limit in `AsymTorus/`) and construct their weak limit as
`Lt → ∞`, landing on the cylinder `S¹_{Ls} × ℝ`. Prove OS0–OS3.

## Current State

**Implemented** (`Pphi2/IRLimit/`):

| File | Status | Axioms | Sorries |
|------|--------|--------|---------|
| `Periodization.lean` | Re-exports from gaussian-field | 0 | 0 |
| `CylinderEmbedding.lean` | `cylinderToTorusEmbed` is a **def**; `cylinderPullback_continuous` **proved** | 2 | 0 |
| `GreenFunctionComparison.lean` | Axiom: uniform 2nd moment (requires OS assumption) | 1 | 0 |
| `UniformExponentialMoment.lean` | Axiom: uniform exp moment (requires OS assumption) | 1 | 0 |
| `IRTightness.lean` | Axiom: Prokhorov extraction with char. functional convergence | 1 | 0 |
| `CylinderOS.lean` | OS0+OS3 axiomatized; OS2 **proved** via weak limit | 3 | 1 |

**Total: 8 axioms + 1 sorry in pphi2, 3 axioms in gaussian-field `Cylinder/MethodOfImages.lean`.**

Changes from initial plan (2026-03-19):
- Removed intermediate axioms `torusGreen_method_of_images` and `wrapAround_exponentially_suppressed` from gaussian-field (subsumed by `torusGreen_uniform_bound`)
- Added `UniformExponentialMoment.lean` for OS0 analyticity
- Proved `cylinderPullback_continuous` (WeakDual continuity)
- Proved OS2 time reflection in `routeBPrime_cylinder_OS` via characteristic functional convergence + torus reflection invariance
- Refined axiom statements: `cylinderIR_uniform_second_moment` and `cylinderIR_uniform_exponential_moment` now require `AsymSatisfiesTorusOS`
- `cylinderIRLimit_exists` now states characteristic functional convergence (not just first moments)
- `cylinderPullback_timeReflection_invariant` now requires torus Θ invariance

## Architecture

```
CylinderTestFunction Ls = NTP(SMC_Ls, Schwartz ℝ)
        │
        │  cylinderToTorusEmbed Lt Ls  (DEF, not axiom)
        │  = swap ∘ (id ⊗ periodize Lt)
        ▼
AsymTorusTestFunction Lt Ls = NTP(SMC_Lt, SMC_Ls)
        │
        │  cylinderPullback Lt Ls  (DEF)
        │  ω_cyl(f) = ω_torus(embed f)
        ▼
Configuration(CylinderTestFunction Ls)
        │
        │  cylinderPullbackMeasure Lt Ls μ  (DEF)
        │  = pushforward of μ under pullback
        ▼
Family of cylinder measures {ν_Lt} indexed by Lt
        │
        │  Prokhorov (axiom: cylinderIRLimit_exists)
        │  Uniform 2nd moment → Mitoma → tightness
        ▼
ν = weak limit  (the P(φ)₂ cylinder measure)
        │
        │  OS axiom transfer (axiom: routeBPrime_cylinder_OS)
        ▼
ν satisfies OS0 + OS2 + OS3
```

## What needs proving

### Axiom 1: `cylinderIR_uniform_second_moment`

**Statement**: For any cylinder test function `f`, the second moment
`E_{ν_Lt}[(ωf)²]` is bounded uniformly in `Lt`.

**Proof route**:
1. `E_{ν_Lt}[(ωf)²] = E_{μ_Lt}[(ω(embed f))²]` (pullback)
2. `E_{μ_Lt}[(ω(embed f))²] ≤ C · G_{Lt,Ls}(embed f, embed f)` (density transfer, proved in AsymTorusOS)
3. `G_{Lt,Ls}(embed f, embed f) ≤ C' · q(f)²` (method of images bound)
   **⚠️ NOT** `G_torus ≤ G_cyl` — the torus sum OVERESTIMATES the cylinder
   integral (coth > 1). Instead use the method of images in position space:
   `G_torus(f,f) = G_cyl(f,f) + Σ_{k≠0} wrap-around terms`
   where the wrap-around terms are exponentially suppressed by the mass gap
   `e^{-m|kLt|}` for Schwartz `f`. The sum is bounded uniformly in `Lt ≥ 1`.

**Estimated effort**: ~350 lines (method of images + absolute summability).

### Axiom 1b: `cylinderIR_uniform_exponential_moment` (NEW — from review)

**Statement**: `E_{ν_Lt}[exp(ω(f))] ≤ exp(C · ‖f‖²)` uniformly in Lt.

Uniform second moments alone don't give OS0 analyticity. Need the
Nelson/Fröhlich exponential bound pulled through the embedding.

**Proof route**: From `asymTorusInteracting_exponentialMomentBound` (proved
in AsymTorusOS) applied to `embed f`, combined with the method of images
bound on `‖embed f‖`.

**Estimated effort**: ~100 lines.

### Axiom 2: `cylinderIRLimit_exists`

**Statement**: The family `{ν_Lt}` has a weakly convergent subsequence.

**Proof route**: Identical to `asymTorusInteractingLimit_exists`:
1. Uniform second moments (from axiom 1)
2. `configuration_tight_of_uniform_second_moments` (gaussian-field)
3. Prokhorov's theorem on the Polish configuration space

**Estimated effort**: ~150 lines (follows template exactly).

### Axiom 3: `routeBPrime_cylinder_OS`

**Statement**: The limit measure satisfies OS0, OS2, OS3.

**Proof route**:

**OS0** (analyticity): Each torus `Z_{Lt}[z]` is entire analytic (from
`asymTorusInteracting_os0`). The limit is analytic by: uniform exponential
moment bounds (axiom 1b) + Montel/Vitali convergence. Without the uniform
exponential bound, weak convergence only gives pointwise convergence of
`Z` on the real axis, which is insufficient for analyticity.

**OS2** (invariance): **Exact, no limiting argument needed.** Periodization
perfectly intertwines continuous time shifts:
`periodize(shift_τ f)(t) = Σ_k f(t - τ + kLt) = (shift_τ (periodize f))(t)`
Therefore `Z_Lt(shift_τ f) = Z_Lt(f)` holds algebraically at every finite
`Lt`. The cylinder pullback is exactly time-translation invariant.
Spatial translation is similarly exact (the spatial circle is common).
Time reflection is exact at each torus.

**OS3** (reflection positivity): **Requires compact support density argument.**
⚠️ A Schwartz positive-time test function `f` has infinite temporal tails.
Its periodization `embed f` wraps the tail into negative time on the torus,
violating the support condition for torus RP.
**Fix**: Restrict to `f ∈ C_c^∞((0,R) × S¹_Ls)` (compactly supported in
positive time). For `Lt > 2R`, `embed f` fits entirely in the positive half
of the torus with no wrap-around, so torus RP applies exactly. Pass through
the weak limit. Then extend to all positive-time Schwartz functions by
density of `C_c^∞((0,∞) × S¹)` in the positive-time subspace.

**Estimated effort**: ~450 lines (OS2: 50, OS3: 200, OS0: 200).

## gaussian-field additions needed

Already added (cylinder branch, pushed):

| File | Content | Axioms |
|------|---------|--------|
| `Nuclear/GeneralMapCLM.lean` | NTP functor for different types | 2 |
| `SchwartzNuclear/Periodization.lean` | `periodizeCLM` | 3 |

Still needed:

| File | Content | Est. |
|------|---------|------|
| `Cylinder/MethodOfImages.lean` | `G_torus = G_cyl + wrap-around` | ~350 lines |

## Dependencies

```
gaussian-field (cylinder branch):
  Nuclear/GeneralMapCLM.lean ← NEW
  SchwartzNuclear/Periodization.lean ← NEW
  Cylinder/MethodOfImages.lean ← TODO (method of images bound)

pphi2:
  AsymTorus/ (0 axioms, 0 sorry) ← DONE
  IRLimit/Periodization.lean (re-export) ← DONE
  IRLimit/CylinderEmbedding.lean (def) ← DONE
  IRLimit/GreenFunctionComparison.lean (1 axiom: uniform 2nd moment) ← TODO
  IRLimit/UniformExponentialMoment.lean (NEW: uniform exp bound) ← TODO
  IRLimit/IRTightness.lean (1 axiom: Prokhorov) ← TODO
  IRLimit/CylinderOS.lean (1 axiom: OS0+OS2+OS3) ← TODO
```

## Order of work

1. **Method of images bound** in gaussian-field (~350 lines)
   → Unblocks `cylinderIR_uniform_second_moment`
2. **Prove `cylinderIR_uniform_second_moment`** in pphi2 (~200 lines)
   → Unblocks tightness
3. **Prove `cylinderIR_uniform_exponential_moment`** in pphi2 (~100 lines)
   → Unblocks OS0 analyticity
4. **Prove `cylinderIRLimit_exists`** in pphi2 (~150 lines)
   → Follows template from AsymTorusInteractingLimit
5. **Prove `routeBPrime_cylinder_OS`** in pphi2 (~450 lines)
   → OS2 (exact, ~50 lines) + OS3 (compact support density, ~200 lines)
   + OS0 (Montel/Vitali + uniform exp bounds, ~200 lines)

Total remaining: ~1250 lines across gaussian-field + pphi2.

## Key mathematical corrections (from Gemini review)

1. **Green's function: torus > cylinder**, not ≤. The Riemann sum
   overestimates the integral (coth > 1). Use method of images
   (position space) instead of Fourier comparison.

2. **OS3 wrap-around**: Periodization of positive-time Schwartz functions
   leaks into negative time on the torus. Restrict to compact support,
   choose Lt large enough for no wrap-around, then use density.

3. **OS0 needs exponential moments**, not just second moments. Add
   `cylinderIR_uniform_exponential_moment` as a separate step.

4. **OS2 is exact**: Periodization intertwines time shifts algebraically.
   No limiting argument needed — the pullback measure is exactly
   time-translation invariant at every finite Lt.
