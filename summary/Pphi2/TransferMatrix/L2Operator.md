# `L2Operator.lean` -- Informal Summary

> **Source**: [`Pphi2/TransferMatrix/L2Operator.lean`](../../Pphi2/TransferMatrix/L2Operator.lean)
>
> **Generated**: 2026-03-20

## Overview
Formalizes the transfer matrix as a bounded linear operator on $L^2(\mathbb{R}^{N_s})$ via the kernel factorization $T = M_w \circ \mathrm{Conv}_G \circ M_w$, where $w(\psi) = e^{-(a/2)h(\psi)}$ and $G(x) = e^{-\frac{1}{2}\|x\|^2}$. Proves self-adjointness, compactness (Hilbert-Schmidt), and obtains the spectral decomposition from the compact self-adjoint spectral theorem.

## Status
**Main result**: 0 axioms, 0 sorries
**Length**: summary generated 2026-03-20; manually refreshed for the Hilbert-Schmidt refactor.

---

### `L2SpatialField`
```lean
abbrev L2SpatialField := MeasureTheory.Lp (alpha := SpatialField Ns) R 2 volume
```
The Hilbert space $L^2(\mathbb{R}^{N_s})$ on which the transfer operator acts.

### `transferWeight`
```lean
def transferWeight (P : InteractionPolynomial) (a mass : R) : SpatialField Ns -> R
```
Weight function $w(\psi) = \exp(-(a/2) \cdot h_a(\psi))$.

### `transferGaussian`
```lean
def transferGaussian : SpatialField Ns -> R
```
Gaussian kernel $G(\psi) = \exp(-\frac{1}{2}\|\psi\|^2)$.

### Key proved theorems:
- **`transferWeight_measurable`** / **`transferWeight_bound`**: $w$ is measurable and essentially bounded.
- **`transferWeight_gaussian_decay`**: $w(\psi) \le C \exp(-\alpha \sum \psi(x)^2)$ (Gaussian decay).
- **`transferGaussian_memLp`**: $G \in L^1$ via $\int e^{-\frac{1}{2}\|x\|^2}\,dx = (2\pi)^{N_s/2}$.
- **`transferGaussian_memLp_two`**: $G \in L^2$ (product of 1D Gaussians).
- **`transferWeight_memLp_two`**: $w \in L^2$ (from Gaussian decay domination).

### `transferOperatorCLM`
```lean
def transferOperatorCLM (P : InteractionPolynomial) (a mass : R) (ha : 0 < a) (hmass : 0 < mass) :
    L2SpatialField Ns ->L[R] L2SpatialField Ns
```
The transfer matrix $T = M_w \circ \mathrm{Conv}_G \circ M_w$ as a CLM on $L^2$.

### `transferOperator_isSelfAdjoint`
$T$ is self-adjoint, from self-adjointness of $M_w$ and $\mathrm{Conv}_G$. Fully proved.

### `integral_operator_l2_kernel_compact` (theorem, re-exported)
Hilbert-Schmidt compactness: if $K \in L^2(\mu \otimes \mu)$ then the corresponding integral operator is compact. Proved in `Pphi2.GeneralResults.HilbertSchmidt` and re-exported from `L2Operator.lean`. Reference: Reed-Simon I, Theorem VI.23.

### `transferOperator_isCompact`
$T$ is compact on $L^2$. Proved from `integral_operator_l2_kernel_compact` via the tensor kernel $K(x,t) = w(x) G(t)$. Fully proved.

### `transferOperator_spectral`
Spectral decomposition: $\exists$ Hilbert basis $\{e_i\}$ and eigenvalues $\{\lambda_i\}$ with $Te_i = \lambda_i e_i$. From `compact_selfAdjoint_spectral`. Fully proved.

---
*This file has **0** axioms and **0** sorries.*
