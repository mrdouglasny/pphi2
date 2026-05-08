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
| `CylinderEmbedding.lean` | `cylinderToTorusEmbed` is a **def**; intertwining theorems proved | 0 | 0 |
| `GreenFunctionComparison.lean` | Pullback second-moment identities | 0 | 0 |
| `UniformExponentialMoment.lean` | Uniform exp/second moments derived from explicit Green-moment input | 0 | 0 |
| `IRTightness.lean` | Prokhorov extraction with char. functional convergence | 0 | 0 |
| `CylinderOS.lean` | OS0/OS2 proved; OS3 transfer proved from eventual pullback RP input | 0 | 0 |

**Total: 0 local Route B′ IR-limit axioms + 0 sorries in pphi2.**

Changes from initial plan (2026-03-19):
- Removed intermediate axioms `torusGreen_method_of_images` and `wrapAround_exponentially_suppressed` from gaussian-field (subsumed by `torusGreen_uniform_bound`)
- Added `UniformExponentialMoment.lean` for OS0 analyticity
- Proved `cylinderPullback_continuous` (WeakDual continuity)
- Proved OS2 time reflection in `routeBPrime_cylinder_OS` via characteristic functional convergence + torus reflection invariance
- Refined moment statements: `cylinderIR_uniform_second_moment` and `cylinderIR_uniform_exponential_moment` are theorems conditional on explicit Green-moment input
- `cylinderIRLimit_exists` now states characteristic functional convergence (not just first moments)
- `cylinderPullback_timeReflection_invariant` now requires torus Θ invariance
- Removed the local OS3 axiom by assuming `CylinderMeasureSequenceEventuallyReflectionPositive` for the pullback sequence and proving the IR-limit transfer

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
        │  Prokhorov extraction (proved in cylinderIRLimit_exists)
        │  Uniform Green-moment input → exp/2nd moments → Mitoma tightness
        ▼
ν = weak limit  (the P(φ)₂ cylinder measure)
        │
        │  OS axiom transfer (proved conditional on explicit family inputs)
        ▼
ν satisfies OS0 + OS2 + OS3
```

## What remains external

Route B′ has no local IR-limit axioms left in `Pphi2/IRLimit`. The remaining
work is to prove the explicit family-level hypotheses for the concrete
asymmetric-torus interacting measures.

### Input 1: `AsymTorusSequenceHasUniformGreenMomentBound`

**Statement**: Eventually in the sequence, every asymmetric-torus measure
satisfies `MeasureHasGreenMomentBound` with the same constants `KG, CG`.
Consumers combine this with `Lt → ∞` to obtain a tail where both the Green
bound and `Lt ≥ 1` hold.

**Proof route**:
1. Prove a volume-uniform P(φ)₂ Green-controlled exponential moment bound for
   the concrete UV-limit asymmetric-torus family.
2. Use `cylinderPullback_expMoment_uniform_bound` and `torusGreen_uniform_bound`
   to obtain the cylinder exponential moment theorem already formalized in
   `UniformExponentialMoment.lean`.

This is not a consequence of abstract `AsymSatisfiesTorusOS.os1`; that clause
allows seminorms with explicit `Lt` growth.

### Input 2: `CylinderMeasureSequenceEventuallyReflectionPositive`

**Statement**: For each fixed finite OS3 matrix on positive-time cylinder test
functions, the cylinder pullback sequence is eventually nonnegative.
If a concrete proof produces full cylinder RP for every index, or eventually
full cylinder RP, this exact input is obtained by the proved bridge theorems
`CylinderMeasureSequenceEventuallyReflectionPositive.of_forall` and
`CylinderMeasureSequenceEventuallyReflectionPositive.of_eventually_full`.

**Proof route**:
1. For compactly supported positive-time tests `f ∈ C_c^∞((0,R) × S¹_Ls)`,
   choose `Lt > 2R`; then `embed f` has no wrap-around and torus RP applies.
2. Transfer RP exactly through `cylinderPullbackMeasure`.
3. Extend to all positive-time cylinder Schwartz tests by density and
   continuity of the finite RP matrix.

⚠️ A Schwartz positive-time test function `f` has infinite temporal tails.
Its periodization `embed f` wraps the tail into negative time on the torus,
so one must prove eventual RP for each fixed matrix, not full RP at every
finite `Lt`.

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
  IRLimit/GreenFunctionComparison.lean (0 axioms) ← DONE
  IRLimit/UniformExponentialMoment.lean (0 axioms; conditional theorem) ← DONE
  IRLimit/IRTightness.lean (0 axioms; conditional theorem) ← DONE
  IRLimit/CylinderOS.lean (0 axioms; conditional theorem) ← DONE
```

## Order of work

1. Prove `AsymTorusSequenceHasUniformGreenMomentBound` for the concrete family.
2. Prove `CylinderMeasureSequenceEventuallyReflectionPositive` for the concrete
   family via no-wrap compact support, torus RP, and density.
3. Feed those inputs into `routeBPrime_cylinder_OS`.

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
