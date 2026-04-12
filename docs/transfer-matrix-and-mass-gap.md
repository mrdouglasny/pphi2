# The Transfer Matrix and the Mass Gap

## The Idea

A two-dimensional Euclidean lattice field theory assigns a real field value
$\phi(t,x)$ to each site of a rectangular grid $\{0,\ldots,N_t-1\} \times
\{0,\ldots,N_s-1\}$. The lattice action $S_a[\phi]$ couples neighboring
sites. The partition function is the integral

$$Z = \int \prod_{t,x} d\phi(t,x)\; e^{-S_a[\phi]}.$$

The key observation is that the action decomposes across time slices.
Grouping the field values at a fixed time $t$ into a "spatial field"
$\psi_t = \phi(t,\cdot) : \text{Fin}\;N_s \to \mathbb{R}$, the action
splits as

$$S_a[\phi] = \sum_{t=0}^{N_t-1} \Bigl[\tfrac{1}{2}\sum_x (\psi_{t+1}(x) - \psi_t(x))^2 + a\cdot h_a(\psi_t)\Bigr]$$

where $h_a(\psi)$ is the spatial action containing the spatial kinetic
energy (discrete gradient squared) and the on-site potential (mass term
plus Wick-ordered interaction polynomial). The sum over $t$ is taken with
periodic boundary conditions.

Each term in the sum couples only two adjacent time slices, so the
Boltzmann weight factorizes into a product of kernels:

$$Z = \int \prod_t d\psi_t \; T(\psi_0,\psi_1)\,T(\psi_1,\psi_2)\cdots T(\psi_{N_t-1},\psi_0) = \operatorname{Tr}(T^{N_t}).$$

Here $T$ is the **transfer matrix** --- an integral operator on
$L^2(\mathbb{R}^{N_s})$, the Hilbert space of square-integrable functions
of the spatial field configuration. The trace formula converts the
statistical-mechanical partition function into the trace of a power of
a single operator.

This is the Euclidean analogue of the time-evolution operator in quantum
mechanics. In Minkowski signature, the transfer matrix corresponds to
$e^{-aH}$ where $H$ is the lattice Hamiltonian and $a$ is the lattice
spacing. The spectrum of $T$ encodes the energy levels.

## The Transfer Kernel

The transfer kernel is defined in `Pphi2/TransferMatrix/TransferMatrix.lean`.
For spatial fields $\psi, \psi' : \text{Fin}\;N_s \to \mathbb{R}$:

$$T(\psi,\psi') = \exp\!\Bigl(-\tfrac{1}{2}\sum_x (\psi(x) - \psi'(x))^2 - \tfrac{a}{2}\,h_a(\psi) - \tfrac{a}{2}\,h_a(\psi')\Bigr).$$

The symmetric split --- half of $h_a(\psi)$ on each side --- ensures
$T(\psi,\psi') = T(\psi',\psi)$. This is proved as
`transferKernel_symmetric`.

The spatial action is

$$h_a(\psi) = \underbrace{\tfrac{1}{2}\sum_x a^{-2}(\psi(x\!+\!1) - \psi(x))^2}_{\text{spatial kinetic}} + \underbrace{\sum_x \bigl(\tfrac{1}{2}m^2\psi(x)^2 + {:}P(\psi(x)){:}_c\bigr)}_{\text{on-site potential}}$$

where the spatial lattice has periodic boundary conditions, $m$ is the
bare mass, $P$ is the interaction polynomial, and $c$ is the Wick ordering
constant.

### Kernel factorization

The kernel has a natural factorization that is central to the entire
operator-theoretic analysis. Define:

- The **weight function** $w(\psi) = \exp(-(a/2)\,h_a(\psi))$, the
  Boltzmann weight for a single half-slice.
- The **Gaussian kernel** $G(\psi) = \exp(-\frac{1}{2}\sum_x \psi(x)^2)$,
  the time-coupling factor.

Then

$$T(\psi,\psi') = w(\psi)\cdot G(\psi - \psi')\cdot w(\psi').$$

As an operator on $L^2(\mathbb{R}^{N_s})$, this reads

$$T = M_w \circ \text{Conv}_G \circ M_w$$

where $M_w$ is multiplication by $w$ and $\text{Conv}_G$ is convolution
with $G$. This factorization is the definition of `transferOperatorCLM`
in `Pphi2/TransferMatrix/L2Operator.lean`.

The three factors are constructed as bounded linear operators on $L^2$
individually:

- $M_w$ is defined in `L2Multiplication.lean` via Holder's inequality
  (since $w$ is bounded: the spatial action is bounded below by
  $-N_s A$ from `wickPolynomial_bounded_below`, giving
  $w(\psi) \le e^{aN_sA/2}$).
- $\text{Conv}_G$ is defined in `L2Convolution.lean` via Young's
  convolution inequality (since $G \in L^1$ --- it is a Gaussian integral).

## Properties of the Transfer Operator

Three structural properties of $T$ drive the spectral analysis. All three
are proved (not axiomatized) from the kernel factorization.

### Self-adjointness

The kernel symmetry $T(\psi,\psi') = T(\psi',\psi)$ makes $T$ a
self-adjoint operator on $L^2$. In the factored form, this follows from
the self-adjointness of $M_w$ (multiplication by a real function is
self-adjoint) and the symmetry of $G$ ($G$ is even:
$G(-\psi) = G(\psi)$, so convolution with $G$ is self-adjoint).

### Compactness (Hilbert-Schmidt)

The kernel $T(\psi,\psi')$ is square-integrable:

$$\int\!\!\int |T(\psi,\psi')|^2\,d\psi\,d\psi' < \infty.$$

This makes $T$ a Hilbert-Schmidt operator, hence compact. The proof
(`transferOperator_isCompact`) factors the $L^2$ norm through the kernel
decomposition: the weight $w$ is bounded, and the Gaussian $G$ is
square-integrable (a product of one-dimensional Gaussian integrals), so
the tensor product bound $\|T\|_{L^2} \le \|w\|_\infty^2 \cdot \|G\|_2$
is finite.

### Positivity-improving

An operator is **positivity-improving** if it maps every nonneg nonzero
function to a function that is strictly positive almost everywhere. The
transfer operator has this property because its kernel is strictly
positive everywhere: $T(\psi,\psi') = e^{(\cdots)} > 0$ since the
exponential is always positive.

The proof (`transferOperator_positivityImproving`) works through the
factorization:

1. If $f \ge 0$ and $f \not\equiv 0$, then $g = M_w f$ satisfies $g \ge 0$
   and $g \not\equiv 0$ (since $w > 0$ everywhere).
2. Convolution with the strictly positive Gaussian maps $g$ to a function
   that is strictly positive a.e.: $(\text{Conv}_G\, g)(\psi) =
   \int G(\psi - \psi')\,g(\psi')\,d\psi' > 0$ because $G > 0$ and $g$
   has positive-measure support. The argument uses translation invariance
   of Lebesgue measure (`measurePreserving_add_left`) and
   `integral_pos_iff_support_of_nonneg_ae`.
3. Multiplying by $w > 0$ preserves strict positivity.

This proof is about 150 lines and is one of the more intricate measure-theoretic
arguments in the project, involving $L^2$ Cauchy-Schwarz
(`L2.integrable_inner`) for integrability of the convolution integrand
and `MeasurePreserving` machinery for the support argument.

### Strict positive definiteness

The transfer operator is also strictly positive definite:
$\langle f, Tf \rangle > 0$ for all $f \ne 0$. This is proved
(`transferOperator_strictly_positive_definite`) from the factorization
and the Fourier theory of the Gaussian kernel.

The key input is that convolution with $G$ is strictly positive definite
on $L^2$, because the Fourier transform of $G$ is strictly positive:
$\hat{G}(k) = (2\pi)^{n/2} e^{-\|k\|^2/2} > 0$ for all $k$. By
Plancherel,

$$\langle f, \text{Conv}_G\, f\rangle = \int |\hat{f}(k)|^2 \hat{G}(k)\,dk > 0$$

for nonzero $f$ (since $\hat{f} \not\equiv 0$ by the injectivity of the
Fourier transform). This Bochner-theory argument is in
`GaussianFourier.lean` and uses a single bridge axiom
(`gaussian_conv_strictlyPD`) connecting to the L2 convolution theorem.

Then $\langle f, Tf\rangle = \langle M_w f, \text{Conv}_G(M_w f)\rangle > 0$
by self-adjointness of $M_w$ and the injectivity of $M_w$ (since $w > 0$).

## Jentzsch's Theorem

With the three properties in hand --- compact, self-adjoint,
positivity-improving --- we invoke **Jentzsch's theorem**, the
infinite-dimensional Perron-Frobenius theorem.

### Statement

Let $T$ be a compact, self-adjoint, positivity-improving operator on
$L^2$ with a Hilbert eigenbasis $\{e_i\}$ and eigenvalues $\{\lambda_i\}$.
Then there exists a distinguished index $i_0$ (the "ground state") such that:

**(a)** $\lambda_{i_0} > 0$ --- the top eigenvalue is strictly positive.

**(b)** $\lambda_{i_0}$ is simple --- if $\lambda_i = \lambda_{i_0}$ then
$i = i_0$.

**(c)** Spectral gap: $|\lambda_i| < \lambda_{i_0}$ for all $i \ne i_0$.

An important non-consequence: Jentzsch does **not** imply all eigenvalues
are positive. The matrix $\bigl(\begin{smallmatrix}1&2\\2&1\end{smallmatrix}\bigr)$
is positivity-improving with eigenvalues $3$ and $-1$.

### Proof

The proof in `JentzschProof.lean` (1082 lines, fully verified, no axioms
or sorries) follows the Courant-Hilbert / Barry Simon variational
approach. It proceeds in seven phases:

**Phase 1: Absolute value inequality.** For a positivity-preserving
operator, $|Tf| \le T|f|$ almost everywhere. The proof decomposes
$f = f^+ - f^-$ with $f^+, f^- \ge 0$, applies $T$ to each part, and
uses the triangle inequality: $|Tf^+ - Tf^-| \le Tf^+ + Tf^- = T|f|$.

**Phase 2: Inner product inequality.** From Phase 1,
$|\langle f, Tf\rangle| \le \langle |f|, T|f|\rangle$. The proof
integrates the pointwise bound $|f(x)(Tf)(x)| \le |f(x)|(T|f|)(x)$
and uses monotonicity of the inner product in the right argument for
nonneg functions.

**Phase 3: Ground state has nonneg absolute value.** If $f$ is a
ground state ($Tf = \lambda_0 f$ with $\lambda_0 = \|T\|$), then $|f|$
is also a ground state. This follows from Phase 2: the Rayleigh quotient
$\langle |f|, T|f|\rangle / \langle |f|, |f|\rangle$ is at least
$\lambda_0$ (using the inequality from Phase 2), and the spectral
theorem gives it is at most $\lambda_0$.

**Phase 4: Ground state is strictly positive.** Since $|f|$ is a nonneg
ground state and $T$ is positivity-improving, $T|f| = \lambda_0 |f|$ is
strictly positive a.e. (from the definition of positivity-improving).
Therefore $|f| > 0$ a.e., which means the ground state does not vanish
on any set of positive measure.

**Phase 5: Constant sign.** Every ground state eigenvector has constant
sign a.e. If a ground state $f$ changed sign on a set of positive measure,
then $|f|$ would be a distinct ground state that is not a scalar multiple
of $f$ (since $f$ has zeros where $|f|$ does not). But Phase 4 shows this
is impossible.

**Phase 6: Simplicity.** The ground state eigenvalue is simple. If two
linearly independent eigenvectors shared the eigenvalue $\lambda_0$, we
could form a linear combination that changes sign, contradicting Phase 5.

**Phase 7: Spectral gap.** For any $i \ne i_0$, $|\lambda_i| < \lambda_{i_0}$.
The eigenvector $e_i$ is orthogonal to the strictly positive ground state
$e_{i_0}$, so $e_i$ must change sign. If $|\lambda_i| = \lambda_{i_0}$,
then $|e_i|$ would be a ground state by the Rayleigh quotient argument,
but $|e_i|$ is linearly independent from $e_{i_0}$ (since $e_i$ is not
nonneg), contradicting simplicity.

### Application to the transfer operator

From Jentzsch's theorem and the strict positive definiteness of $T$, the
formalization derives (`Jentzsch.lean`):

- `transferOperator_inner_nonneg`: $\langle f, Tf\rangle \ge 0$ for all $f$.
- `transferOperator_eigenvalues_pos`: all eigenvalues are strictly positive
  (from $\langle e_i, Te_i\rangle = \lambda_i > 0$).
- `transferOperator_ground_simple`: the leading eigenvalue is simple with
  a strict spectral gap.

The positivity of all eigenvalues uses the strict positive definiteness
rather than Jentzsch alone, since Jentzsch only guarantees the leading
eigenvalue is positive.

## The Hamiltonian and the Mass Gap

The transfer matrix is the exponential of the lattice Hamiltonian:
$T = e^{-aH}$. Inverting, $H = -(1/a)\log T$. Since $T$ has a discrete
spectrum of strictly positive eigenvalues $\lambda_0 > \lambda_1 \ge
\lambda_2 \ge \cdots > 0$, the Hamiltonian has energy levels

$$E_n = -\frac{1}{a}\log\lambda_n.$$

The ordering $\lambda_0 > \lambda_1$ (spectral gap) translates to
$E_0 < E_1$ (ground state has the lowest energy). The **mass gap** is

$$m_{\mathrm{phys}} = E_1 - E_0 = \frac{1}{a}\log\frac{\lambda_0}{\lambda_1} > 0.$$

This is defined as `massGap` and proved positive in `massGap_pos`
(`Pphi2/TransferMatrix/Positivity.lean`). The proof is a one-line
consequence of `energyLevel_gap`, which itself follows from the
monotonicity of the logarithm and the strict inequality
$\lambda_1 < \lambda_0$ from Jentzsch.

## From the Mass Gap to Clustering (OS4)

The spectral gap controls the decay of correlations, which is the content
of Osterwalder-Schrader axiom OS4.

### The spectral decomposition argument

Consider the connected two-point function on the lattice:

$$\langle\phi(t,x)\,\phi(0,y)\rangle - \langle\phi(x)\rangle\langle\phi(y)\rangle.$$

Using the transfer matrix eigendecomposition, insert a complete set of
eigenstates $|n\rangle$ with energies $E_n$ between the two field
operators. The $n = 0$ (ground state) contribution gives the disconnected
piece $\langle\phi(x)\rangle\langle\phi(y)\rangle$. The remainder is

$$\sum_{n \ge 1} \langle\Omega|\hat\phi(x)|n\rangle\,\langle n|\hat\phi(y)|\Omega\rangle\cdot e^{-(E_n - E_0)|t|a}.$$

Since $E_n - E_0 \ge m_{\mathrm{phys}}$ for all $n \ge 1$, every term
in the sum decays at least as fast as $e^{-m_{\mathrm{phys}}|t|a}$:

$$\bigl|\langle\phi(t,x)\,\phi(0,y)\rangle - \langle\phi(x)\rangle\langle\phi(y)\rangle\bigr| \le C(x,y)\cdot e^{-m_{\mathrm{phys}}\,|t|\,a}.$$

The same argument extends to general bounded observables: for $F, G$
bounded and $G_R(\phi) = G(\phi(\cdot + R, \cdot))$ time-translated by $R$,

$$\bigl|\langle F\cdot G_R\rangle - \langle F\rangle\langle G\rangle\bigr| \le C(F,G)\cdot e^{-m_{\mathrm{phys}}\,R\,a}.$$

This exponential clustering is the lattice version of OS4. The constant
$C$ depends on the observables (through their overlaps with excited
states) but the decay rate is universal: it is always the mass gap.

### Ergodicity

Exponential clustering implies ergodicity of the measure with respect to
time translations (`clustering_implies_ergodicity` in
`OS4_Ergodicity.lean`). The argument is elementary: if $A$ is a
time-translation-invariant event, set $F = G = \mathbf{1}_A$. Then
$G_R = G$ for all $R$, so clustering gives $|\mu(A) - \mu(A)^2| = 0$,
hence $\mu(A) \in \{0, 1\}$. Ergodicity is equivalent to uniqueness of
the vacuum in the reconstructed quantum theory.

## What Remains Axiomatized

The mass gap at each fixed lattice spacing $a$ is **proved**: the chain
runs from the kernel factorization through self-adjointness, compactness,
positivity-improving, Jentzsch's theorem, and the logarithmic inversion
to $m_{\mathrm{phys}} > 0$.

The spectral decomposition argument connecting the mass gap to exponential
clustering on the lattice (`two_point_clustering_from_spectral_gap` and
`general_clustering_from_spectral_gap`) is axiomatized. The mathematical
content is the insertion of a complete set of eigenstates and estimation
of the geometric series; the formalization would require trace-class
operator theory not yet available in Mathlib.

The hard remaining piece is **uniformity in the lattice spacing**:

$$\exists\, m_0 > 0,\;\exists\, a_0 > 0,\;\forall\, a \in (0, a_0]:\quad m_{\mathrm{phys}}(a) \ge m_0.$$

This is `spectral_gap_uniform` in `SpectralGap.lean`. The mass gap
could in principle shrink to zero as $a \to 0$, which would destroy
clustering in the continuum limit. Proving the uniform lower bound
requires **cluster expansion** techniques (Glimm-Jaffe-Spencer): a
combinatorial resummation of the perturbation theory that controls the
dressed propagator uniformly. This is the deepest analytic input in the
entire P(Phi)\_2 construction and is beyond the scope of the current
formalization.

There is also an explicit lower bound axiom (`spectral_gap_lower_bound`)
stating $m_{\mathrm{phys}} \ge c \cdot m_{\mathrm{bare}}$ for some
constant $c > 0$ depending on the interaction polynomial. For the free
field ($P = 0$), the mass gap equals the bare mass exactly.

## Summary of the Proof Chain

```
Transfer kernel T(psi,psi') = w(psi) G(psi-psi') w(psi')
    |
    v
T = M_w . Conv_G . M_w  on  L^2(R^Ns)
    |
    +--> Self-adjoint     (kernel symmetry)            [proved]
    +--> Compact          (Hilbert-Schmidt)            [proved]
    +--> Pos-improving    (w > 0, G > 0, convolution)  [proved]
    +--> Strictly PD      (Fourier: G-hat > 0)         [proved, 1 bridge axiom]
    |
    v
Jentzsch's theorem                                     [proved, 1082 lines]
    |
    +--> lambda_0 > 0
    +--> lambda_0 simple
    +--> |lambda_i| < lambda_0  for i != 0
    |
    v
All eigenvalues positive  (strict PD + eigenbasis)     [proved]
    |
    v
Mass gap: m = (1/a) log(lambda_0/lambda_1) > 0        [proved]
    |
    v
Exponential clustering: |<FG_R> - <F><G>| <= C e^{-mR} [axiomatized]
    |
    v
Ergodicity / unique vacuum                             [proved from clustering]
```

## References

- Glimm and Jaffe, *Quantum Physics: A Functional Integral Point of View*,
  Springer, 1987. Chapter 6 (transfer matrix formalism), Chapter 19
  (spectral gap and clustering).
- Simon, *The P(phi)\_2 Euclidean (Quantum) Field Theory*, Princeton, 1974.
  Sections III-IV (transfer matrix, spectral properties, clustering).
- Reed and Simon, *Methods of Modern Mathematical Physics IV: Analysis of
  Operators*, Academic Press, 1978. Theorems XIII.43-44 (Jentzsch's theorem
  for integral operators with positive kernels).
- Courant and Hilbert, *Methods of Mathematical Physics*, Vol. I,
  Wiley-Interscience, 1953. Chapter VI (variational methods for eigenvalue
  problems).
- Simon, *Functional Integration and Quantum Physics*, AMS Chelsea, 2005.
  Section I.13 (Perron-Frobenius for positivity-improving semigroups).
