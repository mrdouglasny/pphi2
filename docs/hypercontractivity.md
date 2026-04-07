# Hypercontractivity in the P(Φ)₂ Construction

## The Problem

We are constructing a P(Φ)₂ quantum field theory by taking a continuum limit
of lattice measures. On the lattice with spacing $a$, the interacting measure is

$$d\mu_a = \frac{1}{Z_a}\, e^{-V_a(\phi)}\, d\mu_{\mathrm{GFF}}(\phi)$$

where $\mu_{\mathrm{GFF}}$ is the Gaussian free field measure and
$V_a = a^2 \sum_x {:}P(\phi(x)){:}_{c_a}$ is the Wick-ordered interaction.

To extract a continuum limit via Prokhorov's theorem, we need **tightness**
of the family $\{\mu_a\}$, which requires uniform moment bounds:

$$\int |\omega(f)|^p\, d\mu_a \leq C \qquad \text{uniformly in } a.$$

These moments are under the **interacting** measure, which we cannot compute
directly. Hypercontractivity is the tool that transfers computable estimates
from the free Gaussian measure to the interacting one.

## The Three Ingredients

The proof (Option A in the code) combines three results via Cauchy–Schwarz.

### 1. Gaussian Hypercontractivity

**Theorem** (`gaussian_hypercontractivity_continuum`). *For the lattice
Gaussian measure pushed forward to the continuum, polynomial functionals
satisfy*

$$\int |\omega(f)|^{pn}\, d(\iota_a)_*\mu_{\mathrm{GFF}}
  \leq (p-1)^{pn/2}\,
  \Bigl(\int |\omega(f)|^{2n}\, d(\iota_a)_*\mu_{\mathrm{GFF}}\Bigr)^{p/2}.$$

This is Nelson's hypercontractive estimate: $L^p$ norms of degree-$n$
polynomial functionals of a Gaussian are controlled by their $L^2$ norms,
with the specific constant $(p-1)^{n/2}$. The deep input is the Gross
log-Sobolev inequality for Gaussian measures (proved in the `gaussian-field`
library). In the formalization, the continuum statement reduces to the
abstract lattice version via `integral_map` and the identity
$(\iota_a\,\omega)(f) = \omega(g_f)$, where $g_f$ is the lattice dual
of the test function $f$.

### 2. Nelson's Exponential Estimate

**Theorem** (`exponential_moment_bound` / `nelson_exponential_estimate_lattice`).
*There exists $K > 0$ depending on $P$, $L$, and $m$ but not on $N$ such that*

$$\int e^{-2V_a}\, d\mu_{\mathrm{GFF}} \leq K.$$

This is the analytic heart of the construction. Its subtlety is easy to
miss. The naive approach — "the Wick polynomial is bounded below per site,
so bound the exponential pointwise" — would give a bound
$\exp(2 N^2 A)$ that diverges as $N \to \infty$. Three things conspire:

1. The Wick constant $c_a \sim \frac{1}{2\pi}\log(1/a)$ diverges as
   $a \to 0$.
2. The per-site lower bound $A$ on $-{:}P(\phi(x)){:}_{c_a}$ depends on
   $c_a$, hence on $a$.
3. The number of lattice sites $|\Lambda| \sim 1/a^2$ grows.

The resolution uses the **physical volume identity**:

$$a^2 \cdot |\Lambda| = \Bigl(\frac{L}{N}\Bigr)^2 \cdot N^2 = L^2.$$

Since $V_a(\omega) = a^2 \sum_x {:}P(\phi(x)){:}_{c_a} \geq -a^2 |\Lambda| A
= -L^2 A$, we get $e^{-2V_a} \leq e^{2L^2 A}$ pointwise, and integrating
over the probability measure $\mu_{\mathrm{GFF}}$ gives $K = e^{2L^2 A}$.

The bound $A$ itself is uniform because the Wick constant satisfies
$c_a \leq m^{-2}$ for all $N$ (proved in `wickConstant_le_inv_mass_sq`),
so `wickPolynomial_uniform_bounded_below` applies with a fixed cutoff.

*Remark.* For the full continuum limit on $\mathbb{R}^2$ (not a torus),
the physical volume is infinite and this simple argument fails. One needs
cluster expansions (Glimm–Jaffe §8.6, Simon §V). The torus formalization
avoids this because $L$ is fixed.

### 3. Cauchy–Schwarz Density Transfer

**Theorem** (`interacting_moment_bound`). *For all $p \geq 2$, $n \in \mathbb{N}$,
and Schwartz test functions $f$:*

$$\int |\omega(f)|^{pn}\, d\mu_a
  \leq C\,(2p-1)^{pn/2}\,
  \Bigl(\int |\omega(f)|^{2n}\, d(\iota_a)_*\mu_{\mathrm{GFF}}\Bigr)^{p/2}$$

*where $C = K^{1/2}$ and the right side uses the free Gaussian measure.*

**Proof.** Since $d\mu_a = \frac{1}{Z_a} e^{-V_a}\, d\mu_{\mathrm{GFF}}$,
Cauchy–Schwarz gives

$$\int F\, d\mu_a
  = \frac{1}{Z_a}\int F \cdot e^{-V_a}\, d\mu_{\mathrm{GFF}}
  \leq \frac{1}{Z_a}
    \Bigl(\int F^2\, d\mu_{\mathrm{GFF}}\Bigr)^{1/2}
    \Bigl(\int e^{-2V_a}\, d\mu_{\mathrm{GFF}}\Bigr)^{1/2}.$$

Applying ingredient (2) to the second factor and ingredient (1) to the
first (with $F = |\omega(f)|^{pn}$, so $F^2 = |\omega(f)|^{2pn}$, which
is a degree-$2pn$ polynomial moment controlled by the $L^2$ norm), we
obtain the result. The partition function bound $Z_a \geq 1$ (by Jensen's
inequality on the convex function $\exp$, using
$\int V_a\, d\mu_{\mathrm{GFF}} \leq 0$ from Hermite orthogonality)
absorbs the $1/Z_a$ factor.

## Why the RHS Must Use the Free Measure

A natural question: why not express the bound entirely in terms of the
interacting measure $\mu_a$? Converting the RHS back from $\mu_{\mathrm{GFF}}$
to $\mu_a$ would require bounding

$$\int e^{+V_a}\, d\mu_{\mathrm{GFF}}.$$

But $V_a \sim \phi^4$ grows faster than the Gaussian suppression
$e^{-\phi^2}$, so this integral **diverges**. The asymmetry is fundamental:
$e^{-V_a}$ is bounded (the interaction stabilizes the theory) while
$e^{+V_a}$ is not. The entire Cauchy–Schwarz strategy is designed to keep
all analytic estimates on the free side.

## Role in the Overall Construction

The logical chain is:

```
Hypercontractivity
    → uniform moment bounds for μ_a
    → tightness of {μ_a}
    → Prokhorov's theorem gives a convergent subsequence
    → continuum limit measure μ exists
    → verify Osterwalder–Schrader axioms for μ
    → OS reconstruction → Wightman QFT in 1+1d
```

Without hypercontractivity, there are no uniform moment bounds, tightness
fails, and the continuum limit cannot be extracted.

## Formalization Details

All three ingredients are fully proved (0 axioms, 0 sorries) in
`Pphi2/ContinuumLimit/Hypercontractivity.lean`. Key proof techniques:

- **Ingredient 1** reduces to the abstract `gaussian_hypercontractive`
  from `gaussian-field` via `integral_map` and `latticeEmbedLift_eval_eq`.
- **Ingredient 2** uses `wickPolynomial_uniform_bounded_below` (the Wick
  polynomial has a uniform lower bound for $c \in [0, m^{-2}]$) combined
  with the physical volume identity $a^2 N^2 = L^2$.
- **Ingredient 3** uses `density_transfer_bound` (a general Cauchy–Schwarz
  lemma for density-weighted measures) and `partitionFunction_ge_one`
  (Jensen's inequality).
- **Wick constant variance identity** (`wickConstant_eq_variance`): proved
  via spectral decomposition of the lattice covariance, using translation
  invariance and the Fourier-mode eigenbasis. This shows $c_a = E[\phi(x)^2]$,
  connecting the abstract Wick constant to the physical variance.

Nelson's exponential estimate also has a more detailed proof infrastructure
in `Pphi2/NelsonEstimate/` (6 files, ~600 lines) implementing the full
covariance splitting and dynamic cutoff argument from Simon §V / Glimm–Jaffe
§8.6, though the simpler physical volume argument suffices for the torus.

## References

- Gross, "Logarithmic Sobolev inequalities," *Amer. J. Math.* **97** (1975),
  1061–1083.
- Nelson, "The free Markoff field," *J. Funct. Anal.* **12** (1973), 211–227.
- Simon, *The P(φ)₂ Euclidean (Quantum) Field Theory*, Princeton, 1974, §V.
- Glimm and Jaffe, *Quantum Physics: A Functional Integral Point of View*,
  Springer, 1987, §8.6 and §19.4.
