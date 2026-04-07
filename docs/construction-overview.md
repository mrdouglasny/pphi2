# End-to-End Overview of the P(Phi)_2 Construction

## 1. Goal

The goal of this project is to construct, in Lean 4, a probability measure
$\mu$ on the space of tempered distributions $\mathcal{S}'(\mathbb{R}^2)$
satisfying all five Osterwalder-Schrader axioms:

- **OS0 (Analyticity):** The generating functional
  $Z[\sum z_i J_i]$ is entire analytic in $z \in \mathbb{C}^n$.
- **OS1 (Regularity):** $|Z[f]| \leq \exp(c(\|f\|_1 + \|f\|_p^p))$
  for some $1 \leq p \leq 2$.
- **OS2 (Euclidean Invariance):** $Z[g \cdot f] = Z[f]$ for all
  $g \in E(2) = \mathbb{R}^2 \rtimes O(2)$.
- **OS3 (Reflection Positivity):** The RP matrix
  $\sum_{ij} c_i c_j \operatorname{Re}(Z[f_i - \Theta f_j]) \geq 0$
  for positive-time test functions.
- **OS4 (Clustering):** $Z[f + T_a g] \to Z[f] \cdot Z[g]$ as
  $\|a\| \to \infty$.

By the Osterwalder-Schrader reconstruction theorem (1973, 1975), any such
measure yields a relativistic Wightman quantum field theory in 1+1
Minkowski spacetime, with a separable Hilbert space, a positive-energy
unitary representation of the Poincare group, a unique vacuum, and
operator-valued tempered distributions satisfying locality. The OS4
clustering property further guarantees a positive mass gap: the lightest
particle in the theory has mass $m_{\mathrm{phys}} > 0$.

This is the theorem originally proved by Glimm and Jaffe (1968--1973),
Nelson (1973), and Simon, with contributions from Guerra, Rosen, and
Simon, among others. The formalization follows the lattice approach
described in Glimm-Jaffe's *Quantum Physics: A Functional Integral
Point of View* and Simon's *The P(phi)_2 Euclidean (Quantum) Field
Theory*.

## 2. Phase 1: The Lattice Measure

### The free field

The starting point is the **lattice Gaussian free field** (GFF) on the
periodic lattice $(\mathbb{Z}/N\mathbb{Z})^2$ with spacing
$a = L/N$. This is a centered Gaussian measure $\mu_{\mathrm{GFF},a}$
on field configurations $\phi : (\mathbb{Z}/N\mathbb{Z})^2 \to
\mathbb{R}$ with covariance

$$\langle \phi(x)\, \phi(y) \rangle
  = (-\Delta_a + m^2)^{-1}(x, y) =: G_a(x, y),$$

where $\Delta_a$ is the lattice Laplacian and $m > 0$ is the bare mass.
The diagonal $G_a(x, x)$ is finite on the lattice but diverges
logarithmically as $a \to 0$:

$$G_a(x, x) = c_a \sim \frac{1}{2\pi} \log(1/a).$$

This divergence is the source of all ultraviolet difficulties.

### Wick ordering

The interaction polynomial $P(\tau) = \lambda \tau^4 + \ldots$ cannot
be evaluated at $\phi(x)$ directly in the continuum, because
$\langle \phi(x)^2 \rangle = \infty$. **Wick ordering** systematically
subtracts the divergent self-contractions. The Wick-ordered monomial
${:}\tau^n{:}_{c_a}$ is defined by the recursion

$${:}\tau^0{:}_c = 1, \quad {:}\tau^1{:}_c = \tau, \quad
{:}\tau^{n+2}{:}_c = \tau \cdot {:}\tau^{n+1}{:}_c
  - (n+1)\, c \cdot {:}\tau^n{:}_c,$$

which coincides with the probabilist's Hermite polynomial
$\mathrm{He}_n(\tau / \sqrt{c})$ scaled by $c^{n/2}$. The resulting
Wick-ordered polynomial ${:}P(\phi(x)){:}_{c_a}$ has
$\langle {:}P(\phi(x)){:}_{c_a} \rangle_{\mathrm{GFF}} = 0$ for
the leading term, removing the worst divergence. The key analytic fact
is that ${:}P{:}_{c_a}$ remains bounded below uniformly in $a$, with a
bound depending on the Wick constant $c_a$ but not on the field value.

See [wick-ordering.md](wick-ordering.md) for a detailed exposition.

### The interacting measure

The lattice interacting measure is

$$d\mu_a = \frac{1}{Z_a}\, e^{-V_a(\phi)}\, d\mu_{\mathrm{GFF},a}(\phi),$$

where the interaction functional is

$$V_a(\phi) = a^2 \sum_{x \in (\mathbb{Z}/N\mathbb{Z})^2}
  {:}P(\phi(x)){:}_{c_a}$$

and $Z_a = \int e^{-V_a}\, d\mu_{\mathrm{GFF},a}$ is the partition
function. The factor $a^2$ is the lattice area element, so $V_a$ is a
Riemann sum approximating the continuum interaction
$\int {:}P(\phi(x)){:}\, d^2x$. The measure $\mu_a$ is well-defined
because $V_a$ is bounded below and $\mu_{\mathrm{GFF},a}$ is a
probability measure on a finite-dimensional space.

## 3. Phase 2: The Transfer Matrix

The transfer matrix is the central analytic tool of the construction.
It connects the lattice measure to spectral theory, and from spectral
theory flow reflection positivity (OS3), the mass gap, and exponential
clustering (OS4).

### Time-slice decomposition

The lattice $(\mathbb{Z}/N\mathbb{Z})^2$ has a natural decomposition
into time slices: rows at fixed time $t \in \mathbb{Z}/N\mathbb{Z}$,
each containing $N$ spatial sites. The lattice action
$S_a = \frac{1}{2}\phi \cdot (-\Delta_a + m^2) \cdot \phi + V_a$
decomposes as a sum of terms coupling adjacent time slices. After
integrating out the temporal nearest-neighbor couplings, the partition
function becomes a trace:

$$Z_a = \operatorname{Tr}(T^N),$$

where $T$ is the **transfer operator** acting on
$L^2(\mathbb{R}^N, d\nu_{\mathrm{spatial}})$, the space of
square-integrable functions of the spatial field configuration
at a single time slice.

### Factorization: $T = M_w \circ \mathrm{Conv}_G \circ M_w$

The transfer operator factors as a composition of three operators:

1. $M_w$: multiplication by the **transfer weight**
   $w(\phi) = \exp(-\frac{1}{2} a \sum_x {:}P(\phi(x)){:})$, which
   encodes the interaction at a single time slice.
2. $\mathrm{Conv}_G$: convolution with the **Gaussian transfer kernel**
   $G(\phi) = \exp(-\frac{1}{2} \sum_{x,y} \phi(x)\, C^{-1}(x,y)\, \phi(y))$,
   which encodes the nearest-neighbor coupling in the time direction.
3. $M_w$: the same multiplication operator again (the interaction is
   split symmetrically between adjacent time slices).

This factorization is the formal content of
`transferOperatorCLM = mulCLM w ∘L convCLM G ∘L mulCLM w` in the
Lean code.

### Key properties of $T$

From the factorization, three properties are proved:

- **Self-adjoint:** $M_w$ is self-adjoint (it is real multiplication)
  and $\mathrm{Conv}_G$ is self-adjoint (the Gaussian kernel is
  symmetric), so $T = M_w \circ \mathrm{Conv}_G \circ M_w$ is
  self-adjoint.

- **Compact:** The convolution kernel $G$ is in $L^2$, and $w$ is in
  $L^2 \cap L^\infty$. The composition $M_w \circ \mathrm{Conv}_G
  \circ M_w$ is therefore a Hilbert-Schmidt operator, hence compact.
  (Reed-Simon I, Theorem VI.23.)

- **Positivity-improving:** If $f \geq 0$ a.e. and $f \not= 0$, then
  $(Tf)(x) > 0$ for a.e. $x$. This follows from $w > 0$ pointwise
  and $\mathrm{Conv}_G$ being strictly positive: the Gaussian kernel
  $G(\phi) > 0$ everywhere, so convolution with it spreads any nonzero
  nonneg function to a strictly positive function.

  The proof that $\mathrm{Conv}_G$ is strictly positive-definite uses
  Bochner's theorem: the Fourier transform of $G$ is a Gaussian,
  hence strictly positive, so $\langle f, G * f \rangle > 0$ for
  $f \neq 0$.

### Reflection positivity (OS3) from the transfer matrix

The transfer matrix gives a clean proof of **lattice reflection
positivity**. The RP matrix for positive-time test functions
$f_1, \ldots, f_n$ and coefficients $c_1, \ldots, c_n$ is

$$\sum_{i,j} c_i c_j \operatorname{Re}\bigl(
  Z_a[f_i - \Theta f_j]\bigr) \geq 0,$$

where $\Theta$ is time reflection $t \mapsto -t$. This follows from
the transfer matrix being a positive operator: the RP matrix is
$\langle v, T^k v \rangle$ for an appropriate vector $v$ constructed
from the test functions, and positivity of $T$ makes this nonneg.

The lattice RP then transfers to the continuum limit: reflection
positivity is preserved under weak limits because the RP condition
involves continuous bounded functions of the generating functional.

## 4. Phase 3: Spectral Gap

### Jentzsch's theorem

With $T$ compact, self-adjoint, and positivity-improving, the
hypotheses of **Jentzsch's theorem** (the infinite-dimensional
Perron-Frobenius theorem) are satisfied. The conclusion is:

1. The leading eigenvalue $\lambda_0 > 0$ is **simple** (multiplicity 1).
2. The corresponding eigenfunction $\Omega_0$ can be chosen strictly
   positive a.e.
3. All other eigenvalues satisfy $|\lambda_k| < \lambda_0$ for
   $k \geq 1$.

In particular, $\lambda_0 > \lambda_1$: there is a **spectral gap**.

### The mass gap

The physical mass gap is defined as

$$m_{\mathrm{phys}} = -\frac{1}{a} \log(\lambda_1 / \lambda_0).$$

The spectral gap $\lambda_0 > \lambda_1$ immediately gives
$m_{\mathrm{phys}} > 0$. For the continuum limit, one needs the
spectral gap to be **uniform** in the lattice spacing $a$. This is
the content of the axiom `spectral_gap_uniform`: there exists
$m_0 > 0$ such that $\operatorname{gap}(a) \geq m_0$ for all
$a \leq a_0$. The physical justification is that P(phi)_2 with
$m > 0$ has no phase transition (Glimm-Jaffe-Spencer), so the mass
gap cannot close.

### Exponential clustering (OS4)

The spectral gap directly implies exponential decay of correlations.
For test functions $f$, $g$ supported at times $0$ and $t$
respectively:

$$|\langle \phi(f)\, \phi(g) \rangle_{\mu_a}
  - \langle \phi(f) \rangle_{\mu_a} \langle \phi(g) \rangle_{\mu_a}|
  \leq C\, e^{-m_{\mathrm{phys}} \cdot t}.$$

This is the lattice version of OS4 (clustering). When the spectral
gap is uniform in $a$, the exponential clustering survives the
continuum limit, giving OS4 for the limit measure.

See [transfer-matrix-and-mass-gap.md](transfer-matrix-and-mass-gap.md)
for more on the transfer operator, and the `TransferMatrix/` directory
(`L2Operator.lean`, `Jentzsch.lean`, `GaussianFourier.lean`) for the
formalization.

## 5. Phase 4: Continuum Limit

This is where the lattice measures become a measure on the infinite-
dimensional space $\mathcal{S}'(\mathbb{R}^2)$, and where the hardest
analytic estimates live.

### Embedding into $\mathcal{S}'$

Each lattice field $\phi : (\mathbb{Z}/N\mathbb{Z})^2 \to \mathbb{R}$
is embedded into $\mathcal{S}'(\mathbb{R}^2)$ via the
**Riemann-sum embedding** $\iota_a$:

$$(\iota_a \phi)(f) = a^2 \sum_{x \in (\mathbb{Z}/N\mathbb{Z})^2}
  \phi(x)\, f(a \cdot x),$$

where $f \in \mathcal{S}(\mathbb{R}^2)$ is a Schwartz test function.
As $a \to 0$, this Riemann sum converges to $\int \phi(x)\, f(x)\,
d^2x$, which is the distributional pairing $\langle \phi, f \rangle$.

The pushforward $\nu_a = (\iota_a)_* \mu_a$ is a probability measure
on $\mathcal{S}'(\mathbb{R}^2)$.

### Tightness

To extract a convergent subsequence from $\{\nu_a\}$, we need
**tightness**: for every $\varepsilon > 0$, there exists a compact
set $K \subset \mathcal{S}'(\mathbb{R}^2)$ with $\nu_a(K) \geq
1 - \varepsilon$ for all $a$. On nuclear spaces like
$\mathcal{S}'(\mathbb{R}^2)$, tightness is established via the
**Mitoma criterion**: a family of measures on $\mathcal{S}'$ is tight
if and only if the family of one-dimensional marginals
$\{\omega \mapsto \omega(f)\}$ is tight for every test function $f$.

The one-dimensional tightness, in turn, follows from **uniform moment
bounds** via Chebyshev's inequality:

$$\nu_a\bigl(\{|\omega(f)| > R\}\bigr)
  \leq \frac{1}{R^p} \int |\omega(f)|^p\, d\nu_a
  \leq \frac{C}{R^p}.$$

### Hypercontractivity

The uniform moment bounds are the analytic heart of Phase 4. They are
established by **Nelson's hypercontractive estimate**, which transfers
moment bounds from the free Gaussian measure to the interacting one.
Three ingredients combine via Cauchy-Schwarz:

1. **Gaussian hypercontractivity:**
   $\|F\|_{L^p(\mu_{\mathrm{GFF}})} \leq (p-1)^{n/2}
   \|F\|_{L^2(\mu_{\mathrm{GFF}})}$ for degree-$n$ polynomial
   functionals $F$. This is Nelson's estimate, derived from the
   Gross log-Sobolev inequality.

2. **Nelson's exponential estimate:**
   $\int e^{-2V_a}\, d\mu_{\mathrm{GFF}} \leq K$ uniformly in $a$.
   The key insight is the **physical volume identity**:
   $a^2 \cdot N^2 = L^2$, so the total interaction $V_a \geq
   -L^2 A$ regardless of $N$, giving $K = e^{2L^2 A}$.

3. **Cauchy-Schwarz density transfer:** Since $d\mu_a =
   (1/Z_a) e^{-V_a}\, d\mu_{\mathrm{GFF}}$, Cauchy-Schwarz gives
   $\int F\, d\mu_a \leq (1/Z_a)(\int F^2\,
   d\mu_{\mathrm{GFF}})^{1/2} (\int e^{-2V_a}\,
   d\mu_{\mathrm{GFF}})^{1/2}$, combining (1) and (2).

See [hypercontractivity.md](hypercontractivity.md) for the full
exposition, and [nelson-estimate.md](nelson-estimate.md) for the
physical volume argument.

### Prokhorov's theorem

With tightness established, **Prokhorov's theorem** extracts a weakly
convergent subsequence: there exist $a_n \to 0$ such that
$\nu_{a_n} \rightharpoonup \mu$ for some probability measure $\mu$ on
$\mathcal{S}'(\mathbb{R}^2)$. This limit measure $\mu$ is the
continuum P(phi)_2 theory.

See [tightness-and-weak-convergence.md](tightness-and-weak-convergence.md)
for tightness, weak convergence, and Prokhorov's theorem.

### Transfer of axioms to the limit

The OS axioms transfer from the lattice to the limit by different
mechanisms:

- **OS0, OS1:** The uniform moment bounds give uniform exponential
  integrability, which transfers analyticity (Vitali's theorem for
  uniform limits of analytic functions) and regularity bounds to the
  limit.

- **OS3:** Reflection positivity is a statement about the
  nonnegativity of a bilinear form built from the generating
  functional. Since the generating functional converges pointwise
  under weak convergence, the RP inequality passes to the limit.

- **OS4:** The uniform spectral gap gives uniform exponential
  clustering at each lattice spacing. Exponential decay of
  correlations with a uniform rate transfers under weak convergence.

## 6. Phase 5: Euclidean Invariance (OS2)

OS2 requires $Z[g \cdot f] = Z[f]$ for all $g \in E(2)$. The
Euclidean group $E(2) = \mathbb{R}^2 \rtimes O(2)$ is generated by
translations and rotations (plus reflections). These are handled
separately.

### Translation invariance

The lattice has exact invariance under **lattice translations**:
shifting $\phi$ by a lattice vector $(j a, k a)$ is a relabeling of
sites that preserves the lattice action and the GFF covariance. For a
**general** translation $v \in \mathbb{R}^2$, the lattice measure is
not exactly invariant (the lattice breaks continuous translation
symmetry).

However, continuous translation invariance is recovered in the limit.
The argument is:

1. Approximate $v$ by a sequence of lattice vectors $w_n$, with
   $|v - w_n| \leq a_n \sqrt{2}/2 \to 0$.
2. Use the bound $|Z_N[T_v f] - Z_N[T_{w_n} f]| \leq
   \sqrt{E[(\omega(T_v f - T_{w_n} f))^2]}$, which goes to zero
   by continuity of the Schwartz test function.
3. Conclude $Z[T_v f] = Z[f]$ for the limit measure.

See [translation-invariance-proof.md](translation-invariance-proof.md)
for the detailed argument.

### Rotation invariance via Ward identity

Rotation invariance is more subtle. The lattice has only the discrete
$D_4$ symmetry group (rotations by multiples of $\pi/2$ and
reflections through axes), not the full $O(2)$. The continuum limit
could in principle retain the lattice anisotropy.

The key insight is a **renormalization group irrelevance** argument.
The operator that breaks rotation invariance (the leading lattice
artifact) has **scaling dimension 4** in two spacetime dimensions.
Since $4 > d = 2$, this operator is *RG-irrelevant*: its coefficient
in the effective action vanishes as $a \to 0$. Concretely, a Ward
identity argument shows that the rotation anomaly satisfies

$$|Z[R_\theta f] - Z[f]| \leq C\, a^2 |\log a|^p$$

for the interacting measure at lattice spacing $a$, where $p$ is a
polynomial power. The $|\log a|^p$ factor (rather than a pure power)
reflects the logarithmic divergences characteristic of the UV, but
**super-renormalizability** of P(phi)_2 ensures these logs appear only
to polynomial power, not as essential divergences. In particular, the
anomaly still vanishes as $a \to 0$, and the limit measure is
rotation-invariant.

This is formalized in `OSProofs/OS2_WardIdentity.lean`.

## 7. Phase 6: Assembly

The main theorem is assembled in `Pphi2/Main.lean`. The statement is:

> **Theorem** (`pphi2_main`). *For any even polynomial $P$ of degree
> $\geq 4$ bounded below and any mass $m > 0$, any continuum limit
> measure $\mu$ obtained from the Glimm-Jaffe/Nelson lattice
> construction satisfies all five OS axioms.*

Each axiom is proved by a different technique:

| OS Axiom | Proof Method | Key Input |
|----------|-------------|-----------|
| OS0 (Analyticity) | Vitali convergence | Uniform exponential moment bounds |
| OS1 (Regularity) | Direct transfer | Hypercontractive moment bounds |
| OS2 (Invariance) | Translation: lattice approx; Rotation: Ward identity | Super-renormalizability ($\dim 4 > d = 2$) |
| OS3 (RP) | Transfer matrix positivity + weak limit inheritance | Lattice RP from $T \geq 0$; closedness under limits |
| OS4 (Clustering) | Uniform spectral gap | Jentzsch/Perron-Frobenius for $T$ |

The theorem `pphi2_exists` provides the existence form: for any
$(P, m)$, there exists a probability measure satisfying all OS axioms.
The theorem `pphi2_wightman` combines this with the OS reconstruction
theorem to conclude the existence of a Wightman QFT in 1+1 dimensions
with a positive mass gap.

Additional results proved in `Main.lean`:

- **Nontriviality:** The two-point function $\langle \phi(f)^2
  \rangle_\mu > 0$ for $f \neq 0$. The interacting two-point function
  dominates the free-field one (correlation inequalities).

- **Non-Gaussianity:** The connected four-point function (fourth
  cumulant) $S_4^c(f,f,f,f) = S_4 - 3 S_2^2 \neq 0$ for some $f$.
  The interaction genuinely modifies the theory.

- **Mass reparametrization invariance:** The continuum limit depends
  only on the total action, not on how the quadratic part is split
  between the Gaussian covariance and the interaction polynomial.

## 8. The Four Routes

The construction is carried out on four spacetimes, each targeting
different OS axioms. This is a deliberate design choice: different
spacetime geometries make different axioms easy, and the project
develops each route to the point where it contributes its natural
axioms.

### Route A: $\mathbb{R}^2$ (Euclidean plane)

The full construction, targeting all five axioms OS0--OS4 on
$\mathcal{S}'(\mathbb{R}^2)$. The continuum limit involves both a UV
limit ($a \to 0$) and an IR limit (volume $\to \infty$). This is the
"official" route for the main theorem. Route A inherits the lattice
interaction and embedding from the general framework, and its OS2 proof
uses the Ward identity for rotation invariance.

### Route B: $T^2_L$ (symmetric torus)

A finite-volume warm-up that isolates the UV limit. The torus has no IR
divergences (volume $L^2$ is fixed), so the analysis is simpler.
OS0--OS2 are proved with **0 local axioms and 0 sorries** in
`TorusInteractingOS.lean`. OS3 is not natural on the torus (no
distinguished time direction with half-spaces), so it is deferred to
the cylinder routes.

See [torus-interacting-os-proof.md](torus-interacting-os-proof.md) for
the torus construction.

### Route B': $T_{L_t, L_s} \to S^1_{L_s} \times \mathbb{R}$ (asymmetric torus to cylinder)

Extends Route B by taking the time circle to infinite circumference.
The construction proceeds in two limits:

1. **UV limit** ($N \to \infty$ at fixed $L_t, L_s$): identical to
   Route B on the asymmetric torus $T_{L_t, L_s}$. OS0--OS2 proved
   with 0 axioms and 0 sorries in `AsymTorusOS.lean`.

2. **IR limit** ($L_t \to \infty$ at fixed $L_s$): the torus measures
   converge weakly to a measure on the cylinder
   $S^1_{L_s} \times \mathbb{R}$, with tightness from
   uniform-in-$L_t$ moment bounds via the **method of images**.

The cylinder $S^1_{L_s} \times \mathbb{R}$ has a natural time axis,
making OS3 (reflection positivity via $t \mapsto -t$) and the transfer
matrix construction natural.

See [ir-limit-overview.md](ir-limit-overview.md) for the cylinder IR
limit.

### Route C: $S^1_L \times \mathbb{R}$ (cylinder, direct)

A direct Nelson/Simon construction on the cylinder, without going
through the torus. The field is expanded in Fourier modes on $S^1_L$,
with each mode evolving as an Ornstein-Uhlenbeck process in the time
direction. The construction uses spatial UV and temporal IR cutoffs.
Preserved in `future/` and not part of the active build.

### Which OS axiom comes from which route?

| OS Axiom | Best Route | Why |
|----------|-----------|-----|
| OS0 (Analyticity) | B, B' | Exponential moment bounds, proved |
| OS1 (Regularity) | B, B' | Clean moment bounds, proved |
| OS2 (Symmetry) | B' or A | B' for cylinder symmetries, A for full $E(2)$ |
| OS3 (Reflection Positivity) | B' or C | Natural time half-space on cylinder |
| OS4 (Clustering) | B' or A | Transfer matrix spectral gap |

## 9. What Remains

The project builds successfully (`lake build`) and the main theorems
(`pphi2_main`, `pphi2_exists`, `pphi2_wightman`) all type-check.
The proof architecture uses **axioms** for unproved analytic and
probabilistic results, with the logical structure connecting them fully
formalized.

As of the latest count: **pphi2 has 27 axioms and 0 sorries**;
the upstream `gaussian-field` library contributes a further small number,
for a combined total of approximately 31 axioms across both projects.

The axioms cluster into several thematic groups:

- **Cluster expansions and uniform bounds** (spectral gap uniformity,
  Nelson's full estimate on $\mathbb{R}^2$): These are the deepest
  analytic results. On the torus, the physical volume identity gives
  the bound for free; on $\mathbb{R}^2$, cluster expansions
  (Glimm-Jaffe Ch. 8, Simon Ch. V) are needed to control the
  infinite-volume limit.

- **Fourier analysis** (convolution representation, Bochner-type
  identities): Standard results connecting Fourier transforms,
  convolutions, and positive-definiteness. The key axiom
  `fourier_representation_convolution` encodes the identity
  $\langle f, g * f \rangle = \int \operatorname{Re}(\hat{g})
  \cdot |\hat{f}|^2$, which is blocked by the absence of an
  $L^2$ convolution theorem in Mathlib.

- **Hilbert-Schmidt compactness** (`integral_operator_l2_kernel_compact`):
  A standard functional analysis result (Reed-Simon I, Thm VI.23)
  that $L^2$ integral kernels define compact operators.

- **Lattice reflection positivity** (`lattice_rp_matrix`): The
  combinatorial/trigonometric identity connecting the RP matrix to the
  transfer matrix. Partially formalized with helper lemmas.

- **Continuum limit OS axioms** (`os0_continuum`, `os3_for_continuum_limit`):
  Analyticity and RP for the limit measure, proved modulo the transfer
  of lattice properties through weak convergence.

- **Ward identity** (`ward_identity_rotation_anomaly`, `anomaly_bound`):
  The rotation anomaly estimate $O(a^2 |\log a|^p)$ from
  super-renormalizability.

Many of these axioms have been progressively proved over the course of
the project. The trajectory has been from approximately 80 axioms down
to 27, with each round of work proving a batch of axioms and updating
the logical dependencies. The Jentzsch theorem, positivity-improving
property, Gaussian strict positive-definiteness, transfer operator
compactness, Nelson's exponential estimate, and Osgood's lemma for
separate analyticity were all initially axioms and are now fully proved
theorems.

## References

- Glimm and Jaffe, *Quantum Physics: A Functional Integral Point of View*,
  Springer, 1987.
- Simon, *The P(phi)_2 Euclidean (Quantum) Field Theory*, Princeton, 1974.
- Nelson, "Construction of quantum fields from Markoff fields,"
  *J. Funct. Anal.* **12** (1973), 97--112.
- Osterwalder and Schrader, "Axioms for Euclidean Green's functions I,"
  *Comm. Math. Phys.* **31** (1973), 83--112.
- Osterwalder and Schrader, "Axioms for Euclidean Green's functions II,"
  *Comm. Math. Phys.* **42** (1975), 281--305.
- Gross, "Logarithmic Sobolev inequalities," *Amer. J. Math.* **97**
  (1975), 1061--1083.
