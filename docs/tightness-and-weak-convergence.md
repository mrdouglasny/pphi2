# Tightness and Weak Convergence

## The Problem: Extracting a Limit in Infinite Dimensions

We have a family of probability measures $\{\mu_a\}$ on the space of
tempered distributions $\mathcal{S}'(\mathbb{R}^2)$, indexed by the
lattice spacing $a > 0$. Each $\mu_a$ is the interacting P(Phi)_2
measure at lattice spacing $a$, pushed forward to the continuum via the
embedding $\iota_a$. As $a \to 0$, we want to extract a limit measure.

On $\mathbb{R}^n$, every sequence of probability measures has a
convergent subsequence (by Helly's selection theorem), provided the
mass doesn't escape to infinity. But $\mathcal{S}'(\mathbb{R}^2)$ is
infinite-dimensional, and sequences of measures on it need not have
convergent subsequences without additional control. **Tightness** is
exactly the condition that provides this control.

## Weak Convergence

A sequence of measures $\mu_n$ **converges weakly** to $\mu$, written
$\mu_n \rightharpoonup \mu$, if

$$\int f\, d\mu_n \to \int f\, d\mu$$

for every bounded continuous function $f$. This is the natural notion of
convergence for probability measures: you cannot expect pointwise
convergence of measures on individual sets (too strong), but you can ask
that all "smooth averages" converge.

In the formalization (`Pphi2/ContinuumLimit/Convergence.lean`), weak
convergence is stated directly in terms of integrals:

```lean
∀ (f : X → ℝ), Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
  Tendsto (fun n => ∫ x, f x ∂(μ (φ n))) atTop (nhds (∫ x, f x ∂ν))
```

For the QFT application, weak convergence means the Schwinger functions
(correlation functions) converge:

$$S_a^{(n)}(f_1, \ldots, f_n)
  = \int \Phi(f_1)\cdots\Phi(f_n)\, d\mu_a
  \to S^{(n)}(f_1, \ldots, f_n).$$

Products like $\Phi(f_1)\cdots\Phi(f_n)$ are not bounded, so extending
weak convergence beyond bounded functions requires the uniform moment
bounds from [hypercontractivity](hypercontractivity.md).

## Tightness

A family of probability measures $\{\mu_\alpha\}$ on a topological space
$X$ is **tight** if for every $\varepsilon > 0$, there exists a compact
set $K \subseteq X$ such that

$$\mu_\alpha(K) \geq 1 - \varepsilon \quad \text{for all } \alpha.$$

In other words: the mass stays concentrated on a common compact set,
uniformly across the entire family. No mass "leaks to infinity."

**Prokhorov's theorem** says that on a Polish space (or more generally
in the setting used here), a tight family of probability measures has a
weakly convergent subsequence. This is the infinite-dimensional
generalization of Helly's theorem.

In the formalization, tightness is stated as:

```lean
axiom continuumMeasures_tight :
    ∀ ε : ℝ, 0 < ε →
    ∃ (K : Set (Configuration (ContinuumTestFunction d))),
      IsCompact K ∧
      ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
      1 - ε ≤ (continuumMeasure d N P a mass ha hmass K).toReal
```

and Prokhorov's extraction (`prokhorov_sequential`,
`prokhorov_configuration_sequential`) is fully proved.

## What Makes Compact Sets in S'?

On $\mathbb{R}^n$, compact = closed + bounded. On
$\mathcal{S}'(\mathbb{R}^2)$, compact sets are much more constrained.
A distribution $\omega \in \mathcal{S}'$ is determined by its values
$\omega(\psi_m)$ on a basis $\{\psi_m\}$ of $\mathcal{S}(\mathbb{R}^2)$.
The compact sets used in the proof are **coordinate boxes**:

$$K_{D,r} = \bigl\{\omega \in \mathcal{S}' :
  |\omega(\psi_m)| \leq D(1+m)^r \text{ for all } m \in \mathbb{N}\bigr\}$$

where $\{\psi_m\}$ is a Dynin-Mityagin basis. Compactness follows
from Tychonoff's theorem: $K_{D,r}$ embeds into the product
$\prod_m [-D(1+m)^r,\, D(1+m)^r]$, which is compact. The key property
of a Dynin-Mityagin space (a complete nuclear space with countable
seminorms) is that these coordinate boxes are indeed compact in the
weak-* topology, and that every distribution can be reconstructed from
its basis coefficients.

## How Tightness is Proved: Mitoma-Chebyshev

The proof (`configuration_tight_of_uniform_second_moments` in
`gaussian-field/Tightness.lean`, fully proved) proceeds in three steps.

### Step 1: Uniform Second Moments

For each test function $f \in \mathcal{S}(\mathbb{R}^2)$, establish

$$\sup_a \int (\omega(f))^2\, d\mu_a(w) < \infty.$$

This is where **hypercontractivity** enters. The interacting measure
$\mu_a$ is controlled by transferring Gaussian estimates via
Cauchy-Schwarz (see [hypercontractivity.md](hypercontractivity.md)).
For the Gaussian case, the bound is simply $\int (\omega(f))^2\, d\mu_{\mathrm{GFF},a} = \langle f, G_a f\rangle$, which converges to the
continuum Green's function.

### Step 2: Banach-Steinhaus (Baire Category Argument)

The pointwise bounds from Step 1 — one for each $f$ — must be promoted
to a **uniform seminorm bound**. This is a functional-analytic step using
the Baire category theorem.

Define sublevel sets $V_n = \{f \in \mathcal{S} : \forall a,\,
\int (\omega(f))^2\, d\mu_a \leq n\}$. These satisfy:

1. **$V_n$ covers $\mathcal{S}$** (by Step 1: every $f$ lands in some
   $V_n$).
2. **Each $V_n$ is closed** (by Fatou's lemma: the map
   $f \mapsto \int (\omega(f))^2\, d\mu$ is lower semicontinuous, so its
   sublevel sets are closed).
3. **Baire category theorem** (using that Schwartz space, as a
   Dynin-Mityagin space, is a Baire space): since countably many closed
   sets cover a Baire space, some $V_n$ has **nonempty interior**. So
   there is a seminorm ball of radius $r$ around some point $x$ inside
   $V_n$.

A **parallelogram identity** argument then extracts the uniform bound.
For any $f$ with $\|f\|_s < r$, both $x + f$ and $x - f$ lie in $V_n$,
so $\int (\omega(x \pm f))^2 \leq n$. Since

$$(a+b)^2 + (a-b)^2 = 2a^2 + 2b^2,$$

we get $\int (\omega(f))^2 \leq n$ (after using nonnegativity of
$\int (\omega(x))^2$). Rescaling gives the uniform bound:

$$\int (\omega(f))^2\, d\mu_a
  \leq M \cdot \|f\|_s^2$$

for a fixed finite set of seminorms $\|\cdot\|_s$ and constant $M$,
uniform in $a$.

### Step 3: Chebyshev + Mitoma

The uniform seminorm bound gives polynomial growth on basis elements:

$$\int (\omega(\psi_m))^2\, d\mu_a \leq B(1+m)^{2s}$$

for some $B, s$ independent of $a$. By **Chebyshev's inequality**:

$$\mu_a\bigl(\{|\omega(\psi_m)| > D(1+m)^r\}\bigr)
  \leq \frac{B(1+m)^{2s}}{D^2(1+m)^{2r}}.$$

Summing over $m$ with $r > s + 1$ (so the series converges), the total
mass outside the coordinate box $K_{D,r}$ is at most $C/D^2$, which can
be made $< \varepsilon$ by choosing $D$ large enough.

This is **Mitoma's criterion** (1983): tightness of measures on
$\mathcal{S}'$ reduces to tightness of the real-valued projections
$\omega \mapsto \omega(f)$, which in turn follows from uniform second
moment bounds.

## The Full Chain

```
Hypercontractivity
    → uniform second moment bounds (∀f: sup_a ∫(ω(f))² dμ_a < ∞)
    → Banach-Steinhaus: uniform seminorm bound (∫(ω(f))² ≤ M·‖f‖²_s)
    → Chebyshev on basis elements + Mitoma: tightness
    → Prokhorov: weakly convergent subsequence μ_{a_k} ⇀ μ
    → continuum limit measure μ exists
    → verify OS axioms for μ
    → OS reconstruction → Wightman QFT in 1+1d
```

## Uniqueness of the Limit

Prokhorov's theorem guarantees a convergent *subsequence*, but it does
not guarantee that the limit is unique. Different subsequences of lattice
spacings $a_n \to 0$ could in principle converge to different measures.
The main theorem (`continuumLimit`) reflects this: it existentially
quantifies over both the subsequence $\phi$ and the limit measure $\nu$.

**When is the limit unique?**

- **Free field (P = 0):** The limit is unique. The characteristic
  functionals $\exp(-\frac{1}{2}\langle f, G_a f\rangle)$ converge
  pointwise to $\exp(-\frac{1}{2}\langle f, G f\rangle)$, and a
  centered Gaussian measure is determined by its covariance (proved in
  `gaussian_measure_unique_of_covariance`).

- **Weak coupling / high mass:** For $\lambda$ small enough or $m$
  large enough, cluster expansion techniques (Glimm-Jaffe-Spencer) prove
  uniqueness. The interacting measure is a small perturbation of the
  Gaussian and the expansion converges.

- **General P:** Uniqueness is *not known* for all P and $m$, and in
  some cases it is *false*. For double-well potentials like
  $P(\tau) = \lambda(\tau^2 - v^2)^2$ at low temperature, there can be
  phase transitions where different subsequences (or different boundary
  conditions) select different limiting measures. This is the
  broken-symmetry phase.

**What this means for the construction:** The main theorem says "there
exists a measure satisfying all OS axioms," not "there exists a *unique*
such measure." This matches the literature. The OS reconstruction
theorem does not require uniqueness: given *any* measure satisfying the
axioms, it produces a valid Wightman QFT. Different limit measures would
give different (but individually valid) quantum field theories,
corresponding to different superselection sectors or phases.

## Formalization Status

| Component | File | Status |
|-----------|------|--------|
| `configuration_tight_of_uniform_second_moments` | `gaussian-field/Tightness.lean` | **Proved** |
| `prokhorov_sequential` | `Convergence.lean` | **Proved** |
| `prokhorov_configuration_sequential` | `Convergence.lean` | **Proved** |
| `continuumMeasures_tight` (R^2) | `Tightness.lean` | Axiom |
| `torusContinuumMeasures_tight` (torus) | `TorusTightness.lean` | **Proved** |
| `torus_interacting_tightness` (torus P(phi)_2) | `TorusInteractingLimit.lean` | **Proved** |
| `continuumLimit` | `Convergence.lean` | **Proved** |

The general Mitoma-Chebyshev criterion and Prokhorov extraction are fully
proved. On the torus (the main route), interacting tightness is fully proved.
The R^2 case remains an axiom because infinite-volume uniform moment bounds
need additional work.

A subtle point: `Configuration(ContinuumTestFunction d)` (the weak-* dual
of Schwartz space) is **not** a Polish space — the weak-* topology on
infinite-dimensional duals is not metrizable. The standard Prokhorov
theorem for Polish spaces does not apply directly. The formalization
handles this by embedding `Configuration E` into the Polish space
$\mathbb{N} \to \mathbb{R}$ via the Dynin-Mityagin basis and applying
Prokhorov there (`prokhorov_configuration` in gaussian-field).

## References

- Mitoma, "Tightness of probabilities on C([0,1]; S') and D([0,1]; S'),"
  *Ann. Probab.* **11** (1983), 989-999.
- Prokhorov, "Convergence of random processes and limit theorems in
  probability theory," *Theory Probab. Appl.* **1** (1956), 157-214.
- Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley, 1999.
- Simon, *The P(phi)_2 Euclidean (Quantum) Field Theory*, Princeton, 1974, Sec. V.
- Glimm and Jaffe, *Quantum Physics: A Functional Integral Point of View*,
  Springer, 1987, Sec. 19.4.
