# `Convergence.lean` — Informal Summary

> **Source**: [`Pphi2/ContinuumLimit/Convergence.lean`](../../Pphi2/ContinuumLimit/Convergence.lean)
>
> **Generated**: 2026-03-20

## Overview
Applies Prokhorov's theorem to extract a weakly convergent subsequence from the tight family of continuum-embedded measures. Contains a fully proved sequential Prokhorov theorem for Polish spaces (using Mathlib's `isCompact_closure_of_isTightMeasureSet` and Levy-Prokhorov metrization), two topological axioms for $\mathcal{S}'(\mathbb{R}^d)$, the continuum limit existence theorem, and a proved witness for `IsPphi2Limit`.

## Status
**Main result**: `prokhorov_configuration_sequential` (`continuumLimit` removed 2026-10-08, issue #63); 3 axioms total
**Length**: 349 lines, 0 definitions + 5 theorems + 3 axioms

---

### `prokhorov_sequential` (theorem, proved)
On a Polish space $X$, if a sequence of probability measures $\{\mu_n\}$ is tight, then it has a weakly convergent subsequence. **Fully proved** from Mathlib.

### `configuration_continuum_polishSpace` (axiom)
$\mathcal{S}'(\mathbb{R}^d) = \text{WeakDual}\ \mathbb{R}\ \mathcal{S}(\mathbb{R}^d)$ is a Polish space.

### `configuration_continuum_borelSpace` (axiom)
$\mathcal{S}'(\mathbb{R}^d)$ has a Borel $\sigma$-algebra compatible with the weak-* topology.

### `prokhorov_configuration_sequential` (theorem, proved)
Sequential Prokhorov extraction on configuration space, derived from `prokhorov_sequential` using the two topological axioms.

### `continuumLimit_nonGaussian` (axiom)
The continuum limit is non-Gaussian for nontrivial $P$: there exists $f$ with $S_4(f,f,f,f) - 3 S_2(f,f)^2 \ne 0$ (nonzero connected four-point function).

### `pphi2_limit_exists` (theorem, proved)
There exists a probability measure $\mu$ on $\mathcal{S}'(\mathbb{R}^2)$ satisfying `IsPphi2Limit`. **Proved** by constructing the Dirac measure at $0$ as a trivial witness.

---
*This file has **0** definitions and **5** theorems (0 with sorry) + **3** axioms.*
