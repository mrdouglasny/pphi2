# `Main.lean` -- Informal Summary

> **Source**: [`Pphi2/Main.lean`](../../Pphi2/Main.lean)
>
> **Generated**: 2026-04-03

## Overview
The top-level assembly file for the $P(\Phi)_2$ construction. States and proves the main theorem (`pphi2_main`), existence (`pphi2_existence`), nontriviality, non-Gaussianity, the honest theorem `bareMassParameter_positive`, and the bundle `pphi2_exists_os_and_massParameter_positive`. The identifiers `pphi2_mass_gap`, `os_reconstruction`, and `pphi2_wightman` are deprecated aliases: the formalized conclusion is only a positive mass **parameter** from the hypothesis `0 < mass`, not Wightman/OS reconstruction in Lean.

## Status
**Main result**: Depends on axioms from upstream files; 1 axiom in this file (`pphi2_nontriviality`)
**Declarations**: 13 theorems + 1 axiom

---

### `pphi2_main`
For any continuum limit measure $\mu$ (satisfying `IsPphi2Limit`), $\mu$ satisfies all five OS axioms (`SatisfiesFullOS`). Delegates to `continuumLimit_satisfies_fullOS`.

### `pphi2_existence`
$\exists \mu$ probability measure on $\mathcal{S}'(\mathbb{R}^2)$ satisfying `SatisfiesFullOS`. Delegates to `pphi2_exists`.

### `pphi2_nontriviality` (axiom)
$\exists \mu$ such that $S_2(f,f) = \int \Phi(f)^2\,d\mu > 0$ for all $f \ne 0$.

### `pphi2_nonGaussianity`
The connected four-point function is nonzero: $\exists f,\; S_4(f,f,f,f) - 3 S_2(f,f)^2 \ne 0$. Uses `continuumLimit_nonGaussian` with lattice spacings $a_n = 1/(n+1) \to 0$.

### `bareMassParameter_positive`
Honest theorem name: formally only $\exists m_0 > 0$ witnessed by the bare mass
hypothesis, with $m_0 = m$. No physical mass-gap identification is proved here.

### `pphi2_mass_gap` (deprecated)
Alias of `bareMassParameter_positive`.

### `massParameter_positive`
$\exists m_0 > 0$ witnessed by the bare mass hypothesis (not deduced from OS axioms; no Minkowski/Wightman layer).

### `pphi2_exists_os_and_massParameter_positive`
$\exists \mu$ satisfying `SatisfiesFullOS` and $\exists m_0 > 0$ as in `massParameter_positive`.

### `os_reconstruction` (deprecated), `pphi2_wightman` (deprecated)
Aliases for `massParameter_positive` and `pphi2_exists_os_and_massParameter_positive` respectively.

### `mass_reparametrization_invariance`, `mass_reparametrization_exists`
The continuum limit is invariant under mass reparametrization via `shiftQuadratic`.

---
*This file has **0** definitions, **13** theorems, and **1** axiom.*
