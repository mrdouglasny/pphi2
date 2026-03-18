# Asymmetric Torus Implementation

## Status: Step 1 (UV limit) COMPLETE

The asymmetric torus T_{Lt,Ls} = (ℝ/Lt ℤ) × (ℝ/Ls ℤ) UV limit is
implemented in `Pphi2/AsymTorus/`:

| File | Status |
|------|--------|
| `AsymTorusEmbedding.lean` | 0 axioms, 0 sorry |
| `AsymTorusInteractingLimit.lean` | 0 axioms, 0 sorry |
| `AsymTorusOS.lean` | **0 axioms, 0 sorry** (OS0–OS2 fully proved) |

## Implementation Model

**Single cutoff N.** Both lattice directions use the same N:
- Lattice sites: `(ℤ/Nℤ)²` (same as symmetric torus)
- Time embedding: `circleRestriction Lt N` (spacing Lt/N)
- Space embedding: `circleRestriction Ls N` (spacing Ls/N)
- Test function space: `AsymTorusTestFunction Lt Ls = NTP(SMC_{Lt}, SMC_{Ls})`

**Geometric-mean spacing.** The Gaussian measure and interaction use
`a_geom = √(Lt·Ls)/N` as the effective lattice spacing:
- Gaussian: symmetric Laplacian at spacing a_geom
- Interaction: V = a_geom² Σ_x :P(φ(x)):_c, cell area = Lt·Ls/N²
- Nelson bound: a_geom² · N² = Lt·Ls (constant physical volume)

**Known limitation:** The Gaussian Laplacian uses the symmetric spacing
a_geom, not per-direction spacings Lt/N and Ls/N. The gaussian-field
package defines `AsymmetricLaplacian` with independent spacings, but it
is not yet wired in. This affects eigenvalue structure when Lt ≠ Ls
but does not affect the UV limit existence proof.

## What was built in gaussian-field

The following were added to the gaussian-field `cylinder` branch:

- `Torus/AsymmetricTorus.lean` — `AsymTorusTestFunction Lt Ls` type,
  `evalAsymTorusAtSite`, `asymTorusLatticeSites`
- `Laplacian/AsymmetricLaplacian.lean` — per-direction spacings
  (defined but not yet used in the interacting measure)
- `evalTorusAtSite_timeReflection` / `_latticeTranslation` — **proved**

## What was built in pphi2

All NTP infrastructure (evalCLM, mapCLM, etc.) works unchanged with
the asymmetric type. Route B proofs adapted with type changes:

1. `AsymTorusEmbedding.lean` — `asymTorusEmbedLift`, `asymTorusInteractingMeasure`,
   `asymTorusContinuumGreen` (all using single N with geometric-mean spacing)
2. `AsymTorusInteractingLimit.lean` — `asymTorusInteractingLimit_exists`
   (weak limit via Prokhorov, same pipeline as symmetric)
3. `AsymTorusOS.lean` — OS0 (analyticity via Osgood + dominated convergence),
   OS1 (regularity from moment bounds), OS2 (time reflection + translation
   fully proved). **0 axioms, 0 sorrys.**

## Previously axiomatized infrastructure (now proved)

All four infrastructure axioms have been proved (2026-03-18):
1. ~~Lattice translation invariance~~ — proved via evalAsymAtFinSite equivariance
2. ~~GF Lipschitz bound~~ — proved via Cauchy-Schwarz + hypercontractivity + tight norm bound
3. ~~Translation continuity~~ — proved via DM expansion + Sobolev isometry + 3-epsilon
4. ~~Lattice approx error vanishes~~ — proved via squeeze using 1-3

## Remaining work (Step 2: IR limit)

Not yet implemented:
- Cylinder test function space
- Embedding maps T_{Lt,Ls} → S¹_{Ls} × ℝ
- Tightness for Lt → ∞ (uniform moment bounds)
- OS3 from transfer matrix (adapt Route C)
- OS4 from spectral gap

See `docs/route-b-prime-plan.md` for the full plan.
