# `GaussianFourier.lean` -- Informal Summary

> **Source**: [`Pphi2/TransferMatrix/GaussianFourier.lean`](../../Pphi2/TransferMatrix/GaussianFourier.lean)
>
> **Generated**: 2026-03-20

## Overview
Proves $\langle f, G*f \rangle > 0$ for nonzero $f \in L^2(\mathbb{R}^n)$ where $G(x)=e^{-\frac{1}{2}\|x\|^2}$ is the Gaussian kernel. The proof uses three steps: (1) $\hat{G}(k) > 0$ for all $k$ (Gaussian Fourier transform is positive), (2) the Fourier representation $\langle f, G*f\rangle = \int \hat{G}(k)\|\hat{f}(k)\|^2\,dk$, (3) Plancherel injectivity ($f \ne 0 \implies \hat{f} \not\equiv 0$).

## Status
**Main result**: axiom-free within `GaussianFourier.lean`
**Length**: 0 public definitions + 5 public theorems + 0 private axioms

---

### `fourier_gaussian_pos`
For $b > 0$: $\operatorname{Re}\bigl(\widehat{e^{-b\|\cdot\|^2}}(w)\bigr) > 0$ for all $w$. Proved via `fourier_gaussian_innerProductSpace`. Fully proved.

### `fourierTransform_lp_eq_fourierIntegral` (private theorem)
Textbook bridge identifying the Lp Fourier transform representative with the Fourier integral for functions in $L^1 \cap L^2$. Proved via Mathlib's tempered-distribution Fourier compatibility, classical Fourier Fubini, and equality of locally integrable functions from compactly supported smooth tests.

### `fourier_representation_convolution` (private theorem)
$\langle f, \mathrm{Conv}_g f\rangle = \int \operatorname{Re}(\hat{g}(w)) \|\hat{f}(w)\|^2\,dw$ for $g \in L^1$ continuous. Proved from `fourierTransform_lp_eq_fourierIntegral` plus the Schwartz/density infrastructure in `GaussianFourier.lean`.

### `inner_convCLM_pos_of_fourier_pos`
If $\operatorname{Re}(\hat{g}(w)) > 0$ for all $w$, then $\langle f, \mathrm{Conv}_g f\rangle > 0$ for $f \ne 0$. Proved from the Fourier representation and Plancherel injectivity.

### `gaussian_conv_strictlyPD`
Gaussian convolution is strictly positive definite on $L^2$: $\langle f, \mathrm{Conv}_G f\rangle > 0$ for $f \ne 0$. Applies `inner_convCLM_pos_of_fourier_pos` with $G(\psi) = e^{-\frac{1}{2}\|\psi\|^2}$. Fully proved.

---
*This file has **0** public definitions and **5** public theorem clusters (0 with sorry) + **0** private axioms.*
