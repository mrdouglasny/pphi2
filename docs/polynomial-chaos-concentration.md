# Polynomial Chaos Concentration: the General Theorem Behind Nelson's Estimate

*Drafted 2026-05-08. The framing as a large-deviations / polynomial-chaos
concentration problem was suggested by Arthur Jaffe in conversation in his
office (and is awaiting his vetting of this writeup). Two-pass vetted by
Gemini deep-think (2026-05-08): pass 1 caught a fatal integration bug in
the original §4 (the polynomial-chaos bound is symmetric in $|F|$, but
$V_a$ is asymmetric, so the direct integration $\int \exp(2|V_a|)$
diverges); pass 2 approved the corrected version below, which retains
the full Glimm–Jaffe / Simon dynamical-cutoff structure and applies
polynomial-chaos concentration only to the rough error $E_R$.*

## Context

Nelson's exponential estimate $\int e^{-2 V_a}\, d\mu_{\rm GFF} \le K$
(uniform in lattice spacing $a$; this is the cutoff used by
Glimm–Jaffe Ch. 8 / Simon Ch. I) is the last analytic input still
axiomatized in `pphi2` after the Phase 2 / PR #14 discharges. Arthur
Jaffe (in conversation in his office) confirmed the proof method is
**large deviations**: the dynamical-cutoff trick (split
$C = C_S(T) + C_R(T)$, choose $T = T(M)$ to balance the smooth lower
bound against the rough-error tail) is a saddle-point / Legendre-transform
optimization in the LD sense, and the underlying tail bound is a
polynomial-chaos concentration inequality.

If we formalize the abstract concentration theorem, all four Cluster A axioms
collapse to short corollaries.

## The abstract theorem

Let $(\Omega, \mathcal F, \mathbb P)$ carry a centered Gaussian process
$(g_x)_{x \in X}$ ($X$ finite or infinite). For $d \in \mathbb N$,
let $\mathcal H^{\le d}$ denote the closed subspace of $L^2(\mathbb P)$
spanned by polynomials of total degree $\le d$ in the $g_x$. (Wiener
chaos: $\mathcal H^{\le d} = \bigoplus_{k \le d} \mathcal H_k$, where
$\mathcal H_k$ is the $k$-th homogeneous chaos.)

**Theorem (polynomial chaos concentration).** *There is a universal
constant $c_d > 0$ depending only on $d$ such that for every centered
$F \in \mathcal H^{\le d}$ (i.e. $\mathbb E F = 0$):*
$$
\mathbb P\bigl(|F| > \lambda \, \|F\|_{L^2}\bigr) \;\le\; 2 \exp\bigl(- c_d \, \lambda^{2/d}\bigr),
\qquad \lambda > 0.
$$
*Equivalently:*
$$
\|F\|_{L^p} \;\le\; (p - 1)^{d/2} \, \|F\|_{L^2},
\qquad p \ge 2 \qquad \text{(Bonami–Nelson)}.
$$

The two forms are equivalent up to multiplicative constants by
Markov + optimization.

The exponent $2/d$ is **sharp**: take $F = g_1^d$ with
$g_1 \sim \mathcal N(0,1)$. Then $\|F\|_{L^2} = \sqrt{\mathbb E[g_1^{2d}]}$
and
$\mathbb P(|g_1^d| > \lambda \|F\|_{L^2}) = \mathbb P(|g_1| > (\lambda \|F\|_{L^2})^{1/d})$
matches the stated decay.

## Proof sketch (three ingredients)

### Ingredient 1: hypercontractivity of OU

For the Ornstein–Uhlenbeck semigroup $T_t$ on $(\Omega, \mathbb P)$ (with
stationary distribution the Gaussian process):
$$
\|T_t f\|_{L^p} \;\le\; \|f\|_{L^q},
\qquad e^{2t} \ge \frac{p - 1}{q - 1}, \quad 1 < q \le p < \infty.
$$
Restricted to homogeneous chaos $\mathcal H_k$, the semigroup $T_t$ acts by
$e^{-k t}$ (eigenfunction expansion), so for $f \in \mathcal H_k$:
$$
e^{-k t} \, \|f\|_{L^p} \;\le\; \|f\|_{L^q},
\qquad \text{i.e.} \qquad \|f\|_{L^p} \;\le\; e^{k t} \, \|f\|_{L^q}.
$$
Choosing $q = 2$ and $e^{2t} = p - 1$:
$$
\|f\|_{L^p} \;\le\; (p - 1)^{k/2} \, \|f\|_{L^2},
\qquad f \in \mathcal H_k, \; p \ge 2.
$$
Triangle inequality across $k = 0, \dots, d$ extends this to
$\mathcal H^{\le d}$ with constant $(p - 1)^{d/2}$ (up to constants
depending on $d$).

### Ingredient 2: Markov / Chebyshev

For any $\lambda, p > 0$:
$$
\mathbb P\bigl(|F| > \lambda \|F\|_{L^2}\bigr)
\;\le\; \frac{\mathbb E |F|^p}{(\lambda \|F\|_{L^2})^p}
\;=\; \left(\frac{\|F\|_{L^p}}{\lambda \|F\|_{L^2}}\right)^p.
$$

### Ingredient 3: optimize $p$

Combining 1 + 2:
$$
\mathbb P\bigl(|F| > \lambda \|F\|_{L^2}\bigr)
\;\le\; \left(\frac{(p - 1)^{d/2}}{\lambda}\right)^p
\;=\; \exp\!\Bigl(p\,\bigl[(d/2) \log(p - 1) - \log \lambda\bigr]\Bigr).
$$
Set $p - 1 = (\lambda / e)^{2/d}$ (so $(d/2) \log(p - 1) - \log \lambda = -d/2$):
$$
\mathbb P\bigl(|F| > \lambda \|F\|_{L^2}\bigr)
\;\le\; \exp\!\Bigl(-(d/2) \, (\lambda/e)^{2/d}\Bigr),
\qquad \lambda \ge e^{d/2}.
$$
For $\lambda < e^{d/2}$ the bound is trivial ($\le 2$). Tightening the
constant gives the cleaner form
$\mathbb P(|F| > \lambda \|F\|_{L^2}) \le 2 \exp(-c_d \, \lambda^{2/d})$.

## Specialization to Cluster A

> **Retraction (2026-05-08, after Gemini vetting).** An earlier draft of this
> section claimed Cluster A could be discharged by integrating the tail of the
> polynomial chaos concentration theorem applied to all of $V_a$ — i.e.
> $\int \exp(2|V_a|) \le 2 + \int_0^\infty 2 e^{2\lambda} \cdot 2 \exp(-c
> (\lambda/\|V_a\|_2)^{1/k}) \, d\lambda$. **This integral diverges**: for
> $k = 2$ (the standard $\phi^4$ case) the integrand is $\exp(2\lambda - c
> \sqrt{\lambda})$, in which the linear $2\lambda$ term dominates the
> stretched-exponential decay. The issue is that the polynomial-chaos bound
> is symmetric in $|F|$, but $V_a$ is highly **asymmetric**: it is bounded
> below modulo Wick shifts (so its left tail is strongly suppressed), while
> the right tail of $V_a$ is genuinely heavy. A symmetric bound is far too
> weak to control $\int \exp(-2 V_a)$, where what matters is the left tail
> of $V_a$ alone.
>
> The conclusion: polynomial-chaos concentration is one of three ingredients
> in the Glimm–Jaffe Ch. 8 / Simon Ch. I dynamical-cutoff proof, **not** a
> shortcut around it. The four Cluster A axioms still need the full
> small-field / large-field decomposition.

The corrected route to discharging Cluster A:

1. **Decompose the field**: $\phi = \phi_S + \phi_R$ via the
   covariance-split $C = C_S(T) + C_R(T)$ already proved in
   `CovarianceSplit.lean`.
2. **Smooth lower bound**: $V_S(\phi_S) \ge -C_1 (1 + |\log T|)^2$
   (small-field classical bound, no probability — already proved as
   `smooth_interaction_lower_bound_log` in `SmoothLowerBound.lean`). The
   smoothness of $\phi_S$ makes the Wick polynomial a *bounded-below*
   classical function on $\phi_S$.
3. **Rough error tail bound**: $E_R = V(\phi) - V_S(\phi_S)$ is a
   degree-$2k$ Wick polynomial in the *rough* field $\phi_R$. Apply
   polynomial chaos concentration **to $E_R$ only**:
   $$
   \mathbb P\bigl(|E_R| > \lambda\bigr)
     \;\le\; 2 \exp\bigl(-c \, \lambda^{2/(2k)} \, T^{-\delta/(2k)}\bigr),
   $$
   the $T^{-\delta/(2k)}$ factor coming from $\|E_R\|_2 \sim T^{\delta/2}$
   (the rough-covariance estimate already in `CovarianceSplit.lean`).
4. **Dynamical cutoff** (the saddle-point / large-deviations step):
   given a target deviation level $M$, choose $T = T(M)$ such that
   $C_1 (\log T)^2 = M/2$, i.e. $T = \exp(-\sqrt{M/(2C_1)})$. Then
   $V(\phi) \le -M$ forces $|E_R| \ge M/2$, so
   $$
   \mathbb P(V \le -M) \;\le\; \mathbb P(|E_R| \ge M/2)
     \;\le\; \exp\bigl(-c' \, \exp(c'' M^{1/2})\bigr) ,
   $$
   doubly exponential. Integrating $\int_0^\infty \exp(2 M) \cdot
   \mathbb P(V \le -M) \, dM < \infty$ gives the uniform bound on
   $\int \exp(-2 V_a) \, d\mu_{\rm GFF}$.

**Mapping to the existing scaffolding.** The four pphi2 Cluster A axioms
are recovered by the four flavours of $\mu_{\rm GFF}$ we use (symmetric
lattice, asymmetric lattice, and their hypercontractive-moment forms).
The polynomial-chaos concentration theorem above replaces the
`True`-stub bodies of `rough_error_Lp_bound` / `rough_error_tail_bound`
in `RoughErrorBound.lean`; the small-field side is already proved; the
$T = T(M)$ optimization and the Schwinger-style integral
$\int \exp(2M) \mathbb P(V \le -M) \, dM$ are the new content of
`NelsonEstimate.lean`.

In the existing scaffolding, the sub-conclusions are:

| `pphi2` file | scaffolded statement | role in the LD argument |
|---|---|---|
| `RoughErrorBound.lean` `rough_error_Lp_bound` | $\|E_R\|_{L^p} \le C \, p^d \, T^{\delta/2}$ | hypercontractivity (Ingredient 1) on the rough chaos component |
| `RoughErrorBound.lean` `rough_error_tail_bound` | $\mathbb P(|E_R| > \lambda) \le \exp(-c \, \lambda^{2/d} \, T^{-\delta/d})$ | Markov + optimize (Ingredients 2 + 3) |
| `SmoothLowerBound.lean` `smooth_interaction_lower_bound_log` | $V_S \ge -C_1 (1 + |\log T|)^2$ | classical small-field bound (no LD) |
| `NelsonEstimate.lean` (currently axiom) | $\int \exp(-2 V) \, d\mu_{\rm GFF} \le K$ | dynamical cutoff: tune $T = T(M)$, integrate |

After the LD theorem lands, all four `True`-stub theorems in
`RoughErrorBound.lean` become specializations, and the `NelsonEstimate.lean`
assembly is just an integral against the tail bound.

## Notes on infinite-dimensional generalisation

For `pphi2` the lattice has finitely many sites, so we never leave the
finite-dimensional Gaussian setting. The infinite-dimensional version
($X$ separable Hilbert space, $(g_x)$ a centered Gaussian on it) holds
verbatim — Janson's *Gaussian Hilbert Spaces* (1997) Ch. 5 gives the
abstract framework. The $c_d$ constants are independent of $\dim X$
because the proof is via OU hypercontractivity, which holds in arbitrary
dimension.

The relevance for the continuum limit: when we eventually do $a \to 0$,
$V_a$ lives in a fixed-rank chaos (degree $2k$ is fixed by the polynomial
$P$), but the underlying Hilbert-space dimension explodes. The constant
$c_d = c_{2k}$ is dimension-independent, which is why the uniform bound
survives.

## Connection to Mathlib

- `Mathlib.Analysis.MeanInequalities` — Hölder/Markov machinery.
- `Mathlib.MeasureTheory.Function.LpSpace` — `L^p` infrastructure.
- `Mathlib.Probability.Distributions.Gaussian` — Gaussian random variables.
- `Mathlib.Analysis.Hypercontractivity` — **does not yet exist**. Could be
  contributed alongside this work.
- The `markov-semigroups` sister project has Bakry-Émery / Brascamp-Lieb
  infrastructure for the OU semigroup that overlaps. Worth a coordination
  pass before starting.

## References

* A. Bonami, *Étude des coefficients de Fourier des fonctions de L^p(G)*,
  Ann. Inst. Fourier 20 (1970). Original `(p−1)^{1/2}` hypercontractivity
  for one Gaussian variable.
* E. Nelson, "The free Markov field," *J. Funct. Anal.* 12 (1973). Generalises
  to OU semigroup; the construction step uses exactly the bound in question.
* J. Glimm and A. Jaffe, *Quantum Physics: A Functional Integral Point of
  View*, Springer (1987), Ch. 8 (dynamical cutoff for `P(φ)_2`).
* B. Simon, *The P(φ)_2 Euclidean (Quantum) Field Theory*, Princeton
  (1974), Ch. I (cleanest exposition of the dynamical-cutoff trick).
* S. Janson, *Gaussian Hilbert Spaces*, Cambridge (1997), Theorem 5.10
  and its corollaries. The abstract concentration theorem in modern form.
* R. Adamczak and P. Wolff, "Concentration inequalities for non-Lipschitz
  functions with bounded derivatives of higher order," *Probab. Theory
  Related Fields* 162 (2015), 531–586. Modern polynomial-chaos
  concentration with explicit constants.
* B. Maurey, *Some deviation inequalities*, Geom. Funct. Anal. 1 (1991).
  An LDP-style perspective on polynomial chaos via entropy arguments.

## Vetting Q&A (Gemini deep-think, 2026-05-08, two passes)

Q1. **Is the bound** $\mathbb P(|F| > \lambda \|F\|_2) \le 2 \exp(-c_d \, \lambda^{2/d})$
**correct as stated**?
*Verdict: yes, exactly correct.* The prefactor $2$ is the standard
union bound for the two-sided absolute-value tail. The constant $c_d$ is
strictly universal and dimension-independent — this is the magic of
the OU semigroup: hypercontractivity depends only on the chaos degree,
not on the dimension of the Gaussian Hilbert space.

Q2. **Cleanest reference?**
*Verdict: Janson, Theorem 5.10.* The gold standard, stated in exactly the
abstract dimension-independent form needed. Adamczak–Wolff is correct but
brings heavy machinery for non-Lipschitz functions that is not needed
here. **Stick to Janson.**

Q3. **Is the chain "polynomial chaos $\to$ tail bound $\to$ integrate to
get $\int \exp(2|V|) \le K$" the standard route?**
*Verdict: NO — invalid for $k \ge 2$.* The integrand
$\exp(2\lambda - c\sqrt\lambda)$ diverges. The polynomial-chaos bound is
symmetric in $|F|$, but $V_a$ is asymmetric (bounded below modulo Wick
shifts, heavy right tail). What matters for $\int \exp(-2V_a)$ is the
left tail of $V_a$ alone, which the dynamical cutoff isolates by
splitting $V = V_S + E_R$ and applying concentration only to $E_R$. See
the **Retraction** in §4 above; Cluster A still needs the full
Glimm–Jaffe Ch. 8 / Simon Ch. I structure.

Q4. **Sharpness of $2/d$ for Wick polynomials.**
*Verdict: strictly saturated.* For large $\phi$, the lower-order Wick
subtractions are negligible, so $\mathopen{:}\phi^d\mathclose{:} \sim
\phi^d$ asymptotically. If $\phi \sim \mathcal N(0,1)$, the tail of
$\phi^d$ is exactly $\exp(-c\lambda^{2/d})$. There is no hidden
stronger concentration that could rescue the divergent integral in Q3.

Q5. **Existing Lean / Mathlib formalization?**
*Verdict: nothing in Mathlib.* `Mathlib.Probability.Distributions.Gaussian`
has basic Gaussian measures, `Mathlib.Analysis.MeanInequalities` has
$L^p$ infrastructure, but the OU semigroup eigenfunction expansion and
the Wiener chaos decomposition are entirely missing.

Q6. **Coordination with `markov-semigroups`.**
*Verdict: yes — land the abstract theorem there.* `markov-semigroups`
already has:
- `MarkovSemigroups/Abstract/Hypercontractivity.lean`: abstract
  `IsHypercontractive` + Gross's equivalence between log-Sobolev and
  hypercontractivity (the LSI $\Rightarrow$ HC direction is currently
  axiomatized pending Bakry–Émery infrastructure).
- `MarkovSemigroups/Abstract/LogSobolev.lean`: log-Sobolev inequality
  framework.
- `MarkovSemigroups/Diffusion/OrnsteinUhlenbeck.lean`: abstract OU
  semigroup with Mehler's formula, marked as Bakry–Émery with $\rho =
  \lambda_{\min}(C^{-1})$ — currently a 45-line skeleton.
- `MarkovSemigroups/Diffusion/BakryEmery.lean`,
  `Diffusion/CarreDuChamp.lean`: $\Gamma_2$ calculus.

Missing in `markov-semigroups`: the **Wiener chaos decomposition**
$L^2(\gamma_C) = \bigoplus_k \mathcal H_k$ with $\mathcal H_k$ as
eigenspaces of the OU number operator (eigenvalue $-k$), and the
explicit Hermite-polynomial / multilinear-functional models for
$\mathcal H_k$. This is the missing-piece that needs to be built before
the polynomial chaos concentration theorem can be stated, let alone
proved.

## Formalization strategy: finite-dim Hermite, not stochastic calculus

Per Gemini's pass-2 advisory: although the abstract theorem (§2) is
naturally stated for arbitrary Gaussian Hilbert spaces, the lattice
approximation in `pphi2` keeps everything **finite-dimensional**. This
buys a major strategic shortcut for the Lean formalization:

* **Avoid Wiener–Itô / stochastic-calculus machinery.** Multiple
  Wiener–Itô integrals require a substantial measure-theory and
  martingale prerequisite stack that Mathlib does not currently have. We
  do not need any of it.
* **Define $\mathcal H_k$ algebraically via multivariate Hermite
  polynomials** evaluated on the finite-dimensional Gaussian vector
  $(g_x)_{x \in \Lambda}$. Because the lattice GFF measure $\gamma_C$
  is non-degenerate on the finite lattice, the (probabilist's) Hermite
  polynomials form a complete orthogonal basis of $L^2(\gamma_C)$, and
  the chaos decomposition $L^2(\gamma_C) = \bigoplus_k \mathcal H_k$ is
  the standard Hermite expansion.
* **Prove the eigenfunction property of the finite-dim OU generator**
  $L = \Delta - x \cdot \nabla$ directly on Hermite polynomials of total
  degree $k$ (eigenvalue $-k$). This is a direct algebraic computation
  on multivariate polynomials and bypasses any infinite-dimensional
  spectral-theorem machinery.

The infinite-dimensional version of the abstract theorem is then a
limit/closure step that we do **not** need to formalize to close the
Cluster A axioms — every $V_a$ on a fixed lattice lives in a finite
chaos space.

A side benefit: the finite-dim Hermite + OU eigenfunction expansion is a
clean self-contained Mathlib contribution, independent of the QFT
application.

## Time budget (revised after Gemini vetting)

The pre-vetting "3-day shortcut to discharge" was based on the integration
chain Gemini retracted in Q3. Restoring the full dynamical-cutoff structure
puts the realistic timeline back at the original Gemini estimate of **6-8
weeks**, broken down as follows:

* **Wiener chaos decomposition + OU eigenfunction expansion** in
  `markov-semigroups`: $L^2(\gamma_C) = \bigoplus_k \mathcal H_k$ with
  $\mathcal H_k$ identified as eigenspaces of the OU number operator.
  Includes the multilinear-functional / Hermite-polynomial model for
  $\mathcal H_k$. ~**1-2 weeks**.
* **Abstract polynomial chaos concentration theorem** (Janson Thm 5.10) in
  `markov-semigroups`, derived from the existing abstract hypercontractivity
  + the new chaos decomposition. ~**1-2 weeks**.
* **Specialize to the GFF** in `gaussian-field` (or directly in `pphi2`):
  $V_a - \mathbb E V_a \in \mathcal H^{\le 2k}$, $\|V_a\|_2 = O(1)$
  uniformly in $N$ via the existing `CovarianceSplit.lean` +
  `HeatKernelBound.lean` infrastructure. ~**3-5 days**.
* **Wire the dynamical cutoff** in `pphi2/NelsonEstimate/`: replace the
  `True`-stub bodies of `rough_error_Lp_bound` /
  `rough_error_tail_bound`; combine with the already-proved
  `smooth_interaction_lower_bound_log` and the new chaos concentration
  theorem; do the $T = T(M)$ optimization in `NelsonEstimate.lean`.
  ~**2-3 weeks** — this is the **bottleneck**: Gemini flags heavy
  measure-theoretic friction in the domain splitting
  $\{|\phi_R| \le R\}$ vs $\{|\phi_R| > R\}$, Gaussian tail bounds on
  the latter, and recombination of the indicator-weighted integrals.
  Worth investing in reusable Mathlib-style domain-splitting +
  Gaussian-tail-integration lemmas, since the same friction recurs in
  any future CQFT-style estimate (Phase 4 `pphi2_nontriviality`, O(N)
  sigma-model mass gap, etc.).
* **Specialize to the four Cluster A axioms** (lattice / asym lattice
  flavours, with and without the hypercontractive normalization):
  ~**2-3 days**.

Total: **6-8 weeks**, matching the original Gemini estimate.

Two reasons this investment pays back beyond Cluster A:

1. **`markov-semigroups` becomes Mathlib-ready** in the OU/hypercontractivity
   branch. Janson Theorem 5.10 in Lean 4 is a substantial probability-library
   contribution in its own right — there is currently nothing comparable
   upstream — and the Wiener-chaos / Hermite-eigenfunction formalization
   is reusable wherever Gaussian polynomial concentration matters.
2. **The dynamical-cutoff machinery transfers** to other CQFT estimates:
   the same domain-splitting + Gaussian-tail-integration scaffolding shows
   up in Phase 4 (`pphi2_nontriviality`, the genuinely non-Gaussian
   discharge) and in any future O(N) sigma-model / Yukawa work in pphi2N
   or sister projects.
