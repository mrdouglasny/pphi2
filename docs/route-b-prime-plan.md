# Route B': Asymmetric Torus → Cylinder

## Overview

Route B' extends Route B (symmetric torus UV limit) to the asymmetric torus
T_{Lt,Ls} = (ℝ/Lt ℤ) × (ℝ/Ls ℤ), with the eventual goal of taking Lt → ∞
to obtain the cylinder S¹_{Ls} × ℝ and proving OS3 (reflection positivity).

## Current Status

**Implemented (AsymTorus/):**
- `AsymTorusEmbedding.lean` — embedding, interacting measure (0 axioms, 0 sorry)
- `AsymTorusInteractingLimit.lean` — continuum limit existence (0 axioms, 0 sorry)
- `AsymTorusOS.lean` — OS0, OS1, OS2 fully proved (**0 axioms, 0 sorry**)

**Not yet implemented:**
- Step 2: IR limit (Lt → ∞) to the cylinder
- OS3 (reflection positivity) on the cylinder
- OS4 (clustering / mass gap) from transfer matrix spectral gap

## Implementation Model

The current implementation uses a **single cutoff N** for both lattice
directions (not independent N_L, N_W):
- Lattice: `(ℤ/Nℤ)²` (same grid as symmetric torus)
- Time embedding: `circleRestriction Lt N` (spacing Lt/N)
- Space embedding: `circleRestriction Ls N` (spacing Ls/N)
- Gaussian measure: symmetric Laplacian with geometric-mean spacing
  `a_geom = √(Lt·Ls)/N`
- Interaction: V = a_geom² Σ_x :P(φ(x)): with cell area Lt·Ls/N²
- Nelson bound: a_geom² · N² = Lt·Ls (physical volume, constant)

**Known limitation:** The Gaussian measure currently uses the symmetric
Laplacian with spacing a_geom, not the asymmetric Laplacian with per-direction
spacings Lt/N and Ls/N. The gaussian-field package has `AsymmetricLaplacian`
(added in 7188e3a) but it is not yet wired into the interacting measure.
This matters for the correct eigenvalue structure when Lt ≠ Ls.

## Construction Plan: Two Limits

### Step 1: UV limit (DONE — AsymTorus/)

For each Lt, Ls > 0, the interacting measure on T_{Lt,Ls} is constructed
as the weak limit of embedded lattice measures as N → ∞.

Route B's proofs of OS0–OS2 apply with minor type changes:
- The NTP structure NTP(SMC_{Lt}, SMC_{Ls}) has the same generic API
- Nelson's estimate: physical volume Lt·Ls is constant in N
- Tightness, weak convergence, OS0–OS2 all transfer

### Step 2: IR limit (PLANNED)

Take Lt → ∞ with Ls fixed. The torus measures {μ_{P,Lt,Ls}} form a
consistent family. Their weak limit is the cylinder measure μ_{P,Ls}.

**Tightness for Lt → ∞:**
- For test functions f supported in a time interval [-T, T]:
  E[(ωf)²] ≤ C · G_{Ls}(f,f) uniformly in Lt
  (cylinder Green's function dominates torus one up to O(exp(-m·Lt)) error)
- Mitoma-Chebyshev gives tightness

**What's needed:**
- Cylinder test function space (Schwartz on ℝ, smooth on S¹_{Ls})
- Embedding maps T_{Lt,Ls} → cylinder
- Tightness + Prokhorov for Lt → ∞

## OS Axioms on the Cylinder (PLANNED)

### OS0–OS2: From Step 1
Direct transfer from the torus (each torus measure satisfies OS0–OS2,
the limit inherits them).

### OS3: Reflection Positivity (NEW — main goal of Route B')
For the cylinder S¹_{Ls} × ℝ with time reflection Θ: (t, x) ↦ (-t, x):
- Lattice RP from transfer matrix positivity (existing in OS3_RP_Lattice.lean)
- Weak limit preserves RP (positive semidefiniteness is closed)

### OS4: Clustering / Mass Gap
From the spectral gap of the transfer matrix (existing in SpectralGap.lean).

## References

- Glimm-Jaffe, *Quantum Physics*, Chapter 19
- Simon, *The P(φ)₂ Euclidean QFT*, Chapter VIII
- Guerra-Rosen-Simon (1975)
