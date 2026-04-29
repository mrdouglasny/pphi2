# `OS4_MassGap.lean` -- Informal Summary

> **Source**: [`Pphi2/OSProofs/OS4_MassGap.lean`](../../Pphi2/OSProofs/OS4_MassGap.lean)
>
> **Generated**: 2026-03-20

## Overview
Derives the exponential clustering property (OS4) from the spectral gap of the transfer matrix Hamiltonian. On the periodic lattice, the connected two-point function decays against the **cyclic torus time separation**
$d_{\mathrm{cyc}}(t) = \min(t, N-t)$:
$|\langle\phi(t,x)\phi(0,y)\rangle_c| \le C \exp(-m_{\mathrm{phys}} d_{\mathrm{cyc}}(t) a)$
where $m_{\mathrm{phys}} = E_1 - E_0 > 0$. Also defines the connected two-point function and proves it is symmetric and positive semidefinite.

## Status
**Main result**: 2 axioms (`two_point_clustering_from_spectral_gap`, `general_clustering_from_spectral_gap`)
**Length**: 298 lines, 1 definition + 6 theorems + 2 axioms

---

### `two_point_clustering_from_spectral_gap` (axiom)
Two-point clustering on the periodic torus:
$|\langle\phi(t,x)\phi(0,y)\rangle - \langle\phi(x)\rangle\langle\phi(y)\rangle|
\le C \exp(-m_{\mathrm{phys}} \, d_{\mathrm{cyc}}(t)\, a)$.
From inserting a complete set of eigenstates in the transfer matrix trace.

### `general_clustering_from_spectral_gap` (axiom)
General clustering for bounded observables with `G` evaluated on the time-shifted configuration:
$|\langle F(\omega)\,G(\tau_R\omega)\rangle - \langle F\rangle\langle G\rangle|
\le C_{FG} \exp(-m_{\mathrm{phys}} \, d_{\mathrm{cyc}}(R)\, a)$.

### `two_point_clustering_lattice`
Exponential clustering of the two-point function on the lattice. Delegates to the axiom. Fully proved (modulo axiom).

### `general_clustering_lattice`
Exponential clustering for general observables with rate $m = m_{\mathrm{phys}}$. Fully proved (modulo axiom).

### `clustering_uniform`
Uniform clustering: the mass gap is bounded below uniformly in $a$. Delegates to `spectral_gap_uniform`. Fully proved (modulo that axiom).

### `connectedTwoPoint`
```lean
def connectedTwoPoint (d N : N) [NeZero N] (P : InteractionPolynomial) (a mass : R)
    (ha : 0 < a) (hmass : 0 < mass) (f g : FinLatticeField d N) : R
```
Connected two-point function: $G_c(f,g) = \langle\omega(f)\omega(g)\rangle - \langle\omega(f)\rangle\langle\omega(g)\rangle$.

### `connectedTwoPoint_symm`
$G_c(f,g) = G_c(g,f)$. From commutativity of multiplication. Fully proved.

### `connectedTwoPoint_nonneg_delta`
$G_c(\delta_x, \delta_x) \ge 0$. This is variance nonnegativity: $\mathrm{Var}[\omega(\delta_x)] \ge 0$. Fully proved via $\int (X-c)^2 \ge 0$.

---
*This file has **1** definition and **6** theorems (0 with sorry) + **2** axioms.*
