# `Hypercontractivity.lean` — Informal Summary

> **Source**: [`Pphi2/ContinuumLimit/Hypercontractivity.lean`](../../Pphi2/ContinuumLimit/Hypercontractivity.lean)
>
> **Generated**: 2026-03-20

## Overview
Bounds $L^p$ moments of the interacting measure $\mu_a$ in terms of the free Gaussian measure $\mu_{\text{GFF}}$ via Cauchy-Schwarz density transfer. The main chain: Gaussian hypercontractivity (proved from gaussian-field) $\to$ exponential moment bound (proved) $\to$ Cauchy-Schwarz density transfer (proved) $\to$ interacting moment bound (proved). Also proves partition function lower bound $Z_a \ge 1$ via Jensen's inequality, Wick ordering properties, and Hermite orthogonality.

## Status
**Main result**: `interacting_moment_bound` fully proved; 2 axioms
**Length**: 766 lines, 1 definition + 9 theorems + 2 axioms

---

### `gaussian_hypercontractivity_continuum` (theorem, proved)
Gaussian hypercontractivity in continuum-embedded form: $\int |\omega(f)|^{pn}\, d(\iota_a)_* \mu_{\text{GFF}} \le (p-1)^{pn/2} \left(\int |\omega(f)|^{2n}\, d(\iota_a)_* \mu_{\text{GFF}}\right)^{p/2}$. **Proved** by pulling back through `integral_map` and applying `gaussian_hypercontractive` from gaussian-field.

### `wickConstant_eq_variance` (axiom)
The Wick constant $c_a = \langle T(\delta_x), T(\delta_x) \rangle = E[(\omega(\delta_x))^2]$ equals the GFF variance at a site.

### `gaussian_hermite_zero_mean` (axiom)
Probabilist's Hermite polynomial of order $n \ge 1$ has zero mean under matching Gaussian: $\int \text{He}_n(t; \sigma^2)\, dN(0,\sigma^2)(t) = 0$.

### `wickMonomial_latticeGaussian` (theorem, proved)
Wick monomials $:x^n:_c$ of order $n \ge 1$ have zero Gaussian mean. **Proved** from `gaussian_hermite_zero_mean` + marginal Gaussianity + pushforward.

### `interactionFunctional_mean_nonpos` (theorem, proved)
$\int V_a\, d\mu_{\text{GFF}} \le 0$. **Proved** from Hermite orthogonality and $P.\text{coeff}_0 \le 0$.

### `partitionFunction_ge_one` (theorem, proved)
$Z_a \ge 1$. **Proved** by Jensen's inequality applied to the convex function $\exp$.

### `density_transfer_bound` (lemma, proved)
For nonneg $F$: $\int F\, d\mu_{\text{int}} \le K^{1/2} (\int F^2\, d\mu_{\text{GFF}})^{1/2}$. **Proved** via Cauchy-Schwarz (Holder $p=q=2$).

### `interacting_moment_bound` (theorem, proved)
Given a spacing $a \le 1$ and a bound $\int e^{-2V_a}\, d\mu_{\text{GFF}} \le K$ at that $a$: $\int |\omega(f)|^{pn}\, d\mu_a \le K^{1/2} (2p-1)^{pn/2} (\int |\omega(f)|^{2n}\, d\mu_{\text{GFF}})^{p/2}$. **Proved** by chaining density transfer + hypercontractivity. The constant is not uniform in $a$ at fixed $N$ (the former `exponential_moment_bound` was removed 2026-10-08 as false, issue #63).

---
*This file has **1** definition and **9** theorems/lemmas (0 with sorry) + **2** axioms.*
