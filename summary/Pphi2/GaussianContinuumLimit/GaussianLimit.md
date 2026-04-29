# `GaussianLimit.lean` — Informal Summary

> **Source**: [`Pphi2/GaussianContinuumLimit/GaussianLimit.lean`](../../Pphi2/GaussianContinuumLimit/GaussianLimit.lean)
>
> **Generated**: 2026-03-20

## Overview
Assembles the Gaussian continuum limit: existence of a subsequential weak limit, nontriviality ($\int (\omega f)^2\, d\mu > 0$ for $f \ne 0$), Gaussianity of weak limits (proved via characteristic-function convergence / Bochner-Minlos uniqueness), the `IsGaussianContinuumLimit` predicate, and a bridge theorem connecting Gaussian uniform moments to interacting tightness.

## Status
**Main result**: `gaussianContinuumLimit_exists` proved; 0 axioms
**Declarations**: 1 structure + 4 theorems

---

### `gaussianContinuumLimit_exists` (theorem, proved)
For $a_n \to 0$, the embedded Gaussian measures have a weakly convergent subsequence. **Proved** from `gaussianContinuumMeasures_tight` + `prokhorov_configuration_sequential`.

### `gaussianContinuumLimit_nontrivial` (theorem, proved)
$\int (\omega f)^2\, d\mu > 0$ for $f \ne 0$, given the two-point function equals $G(f,f)$. **Proved** from `continuumGreenBilinear_pos`.

### `gaussianLimit_isGaussian` (theorem, proved)
Weak limits of Gaussian measures are Gaussian. If $\mu_n$ are centered Gaussian and $\mu_n \rightharpoonup \mu$, then the limit characteristic functional is still Gaussian, so $\mu$ is Gaussian with the limiting covariance.

### `IsGaussianContinuumLimit` (structure)
```lean
structure IsGaussianContinuumLimit (μ : ...) (mass : ℝ) : Prop
```
Predicate: $\mu$ is a probability measure, Gaussian, has covariance $= G(f,f)$, and is $\mathbb{Z}_2$-symmetric.

### `gaussian_feeds_interacting_tightness` (theorem, proved)
The Gaussian uniform bound $E_{\text{GFF}}[\Phi_a(f)^2] \le C$ feeds the interacting tightness via Cauchy-Schwarz.

---
*This file has **1** structure and **4** theorems (0 with sorry, 0 axioms).*
