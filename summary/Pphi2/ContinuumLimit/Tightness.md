# `Tightness.lean` — Informal Summary

> **Source**: [`Pphi2/ContinuumLimit/Tightness.lean`](../../Pphi2/ContinuumLimit/Tightness.lean)
>
> **Generated**: 2026-03-20

## Overview
States the tightness of the family of continuum-embedded interacting measures $\{\nu_a\}_{a \in (0,1]}$ on $\mathcal{S}'(\mathbb{R}^d)$. This is the key prerequisite for Prokhorov extraction. The proof is axiomatized, relying on Mitoma's criterion (tightness of 1D projections from uniform second moment bounds) fed by hypercontractive estimates.

## Status
**Main result**: `continuumMeasure_sq_integrable` (proved). `continuum_second_moment_uniform` and `continuumMeasures_tight` were removed 2026-10-08 (issue #63): their proofs rested on the false axiom `nelson_exponential_estimate_master_bounded`; the statements themselves are not refuted.

---

### `continuumMeasure_sq_integrable` (theorem, proved)
For each $a > 0$ and Schwartz $f$, $(\omega f)^2$ is integrable under the continuum-embedded interacting measure $\nu_a$.

---
*This file has **0** definitions and **1** theorem (0 with sorry).*
