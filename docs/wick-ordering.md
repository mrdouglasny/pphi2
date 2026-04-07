# Wick Ordering and Renormalization in the P(Phi)_2 Construction

## The Problem: Self-Contraction Divergences

The naive definition of a P(Phi)_2 interaction is

$$V(\phi) = \int_{\mathbb{R}^2} P(\phi(x))\, dx$$

where $P(\tau) = \lambda \tau^4 + \ldots$ is a polynomial. The trouble is
that $\phi(x)$ is not a function but a distribution: the Gaussian free field
(GFF) on $\mathbb{R}^2$ has covariance

$$\langle \phi(x)\, \phi(y) \rangle = G(x, y) = \frac{1}{(-\Delta + m^2)^{-1}}(x, y)$$

and $G(x, x) = +\infty$. The Green's function diverges logarithmically on
the diagonal:

$$G(x, y) \sim -\frac{1}{2\pi} \log |x - y| \quad \text{as } |x - y| \to 0.$$

Consequently, the expectation $\langle \phi(x)^2 \rangle = G(x, x) = \infty$,
and every monomial $\phi(x)^n$ with $n \geq 2$ has infinite variance. Inserting
$P(\phi(x))$ into the path integral produces meaningless infinities.

On a finite lattice with spacing $a$, the Green's function is regularized:
$G_a(x, x) = c_a < \infty$, but $c_a \to \infty$ as $a \to 0$. Any
construction based on naively writing $P(\phi(x))$ will blow up in the
continuum limit. The solution is **Wick ordering**: a systematic subtraction
of self-contractions that removes the divergences.

## What Wick Ordering Does

### The recursion

The Wick-ordered monomial ${:}\tau^n{:}_c$ with variance parameter $c$ is
defined by the two-step recursion

$${:}\tau^0{:}_c = 1, \qquad {:}\tau^1{:}_c = \tau,$$
$${:}\tau^{n+2}{:}_c = \tau \cdot {:}\tau^{n+1}{:}_c - (n+1)\, c \cdot {:}\tau^n{:}_c.$$

This subtracts "self-contractions" order by order. Each time we would form
$\tau \cdot {:}\tau^{n+1}{:}$, we remove $c$ times each of the $(n+1)$
possible contractions of the new factor with an existing one, where $c$ is
the propagator at coinciding points.

### Explicit examples

The first few Wick-ordered monomials are:

$$\begin{aligned}
{:}\tau^2{:}_c &= \tau^2 - c, \\
{:}\tau^3{:}_c &= \tau^3 - 3c\tau, \\
{:}\tau^4{:}_c &= \tau^4 - 6c\tau^2 + 3c^2.
\end{aligned}$$

At $c = 0$, Wick ordering is trivial: ${:}\tau^n{:}_0 = \tau^n$.

### Connection to Hermite polynomials

When $c > 0$, the Wick-ordered monomial is a scaled probabilist's Hermite
polynomial:

$${:}\tau^n{:}_c = c^{n/2}\, \mathrm{He}_n\!\left(\frac{\tau}{\sqrt{c}}\right)$$

where $\mathrm{He}_n$ is the probabilist's Hermite polynomial (Mathlib's
`Polynomial.hermite`). This identity is proved in the formalization via
the Hermite three-term recurrence from the `gaussian-field` library
(`wick_eq_hermiteR_rpow`).

The Hermite connection immediately yields the key orthogonality property:
if $\mu = N(0, c)$ is the Gaussian measure with variance $c$, then

$$\int {:}\tau^n{:}_c \, d\mu = 0 \qquad \text{for all } n \geq 1.$$

This is the defining property of Wick ordering -- it subtracts exactly the
terms needed to make each Wick monomial orthogonal to all lower-order ones
in $L^2(\mu)$.

### The Wick-ordered interaction polynomial

Given an interaction polynomial $P(\tau) = \frac{1}{n}\tau^n + \sum_{m < n} a_m \tau^m$,
the Wick-ordered version replaces each monomial with its Wick-ordered
counterpart:

$${:}P(\tau){:}_c = \frac{1}{n}\, {:}\tau^n{:}_c + \sum_{m < n} a_m\, {:}\tau^m{:}_c.$$

## The Wick Constant

On the periodic lattice $\Lambda_a$ with $N$ sites per side and spacing $a$,
the Wick ordering constant is the diagonal of the lattice Green's function:

$$c_a = G_a(x, x) = \frac{1}{|\Lambda|} \sum_{k} \frac{1}{\lambda_k}$$

where $|\Lambda| = N^d$ is the number of lattice sites and

$$\lambda_k = \frac{4}{a^2} \sum_{i=1}^{d} \sin^2\!\left(\frac{\pi k_i}{N}\right) + m^2$$

are the eigenvalues of $-\Delta_a + m^2$. The expression is independent of
$x$ by translation invariance.

Physically, $c_a$ is the **variance of the field at a single lattice site**:
$c_a = \langle \phi(x)^2 \rangle_{\mathrm{GFF}}$.

### Ultraviolet behavior

In $d = 2$ dimensions, as $a \to 0$ (with $N = L/a \to \infty$ at fixed
physical volume $L^2$), the Wick constant diverges logarithmically:

$$c_a \sim \frac{1}{2\pi} \log\frac{1}{a} + O(1).$$

This is the only UV divergence in P(Phi)_2. The Wick ordering subtraction
${:}\tau^2{:}_{c_a} = \tau^2 - c_a$ removes exactly this divergence from the
quadratic term, and the higher subtractions (like $-6c_a\tau^2 + 3c_a^2$ in
${:}\tau^4{:}_{c_a}$) remove the cascading divergences from higher powers.

### The uniform upper bound

Despite the divergence as $a \to 0$, the Wick constant satisfies a crucial
**uniform upper bound**:

$$c_a \leq \frac{1}{m^2}$$

for all $N$ and $a$, as long as $m > 0$. The proof is elementary: each
eigenvalue satisfies $\lambda_k \geq m^2$, so each inverse satisfies
$1/\lambda_k \leq 1/m^2$, and the average of terms each bounded by $1/m^2$
is at most $1/m^2$. This bound is proved as `wickConstant_le_inv_mass_sq`
and is essential for the Nelson exponential estimate that controls the
partition function.

## Super-Renormalizability: Why Only One Counterterm

In $d = 2$ spacetime dimensions, the only UV divergence in P(Phi)_2 is the
**logarithmic divergence** of the Wick constant $c_a$. This is a consequence
of super-renormalizability: power counting in $d = 2$ shows that the only
primitively divergent diagrams are the tadpoles (self-contractions), and
these diverge only logarithmically.

Concretely, this means:

- **No coupling constant renormalization.** The coefficient $\lambda$ in
  $\lambda \phi^4$ does not need to be adjusted as $a \to 0$.
- **No wave function renormalization.** The kinetic term $(\nabla \phi)^2$
  does not acquire a divergent $Z$-factor.
- **No mass renormalization** beyond Wick ordering. The Wick subtraction
  $-c_a$ already absorbs the mass divergence.

The single operation of Wick ordering -- replacing $\tau^n$ with
${:}\tau^n{:}_{c_a}$ -- is the **only** renormalization needed.

This stands in sharp contrast to $d = 4$, where $\phi^4$ theory requires
infinitely many counterterms (mass, coupling, wave function renormalization
at each loop order, and ultimately the theory is believed to be trivial).
Super-renormalizability is what makes the P(Phi)_2 construction
mathematically tractable.

## The Interacting Measure

### Definition

The P(Phi)_2 lattice measure is defined as a density perturbation of the
lattice Gaussian free field measure:

$$d\mu_a = \frac{1}{Z_a}\, e^{-V_a(\phi)}\, d\mu_{\mathrm{GFF}}(\phi)$$

where the Wick-ordered lattice interaction is

$$V_a(\phi) = a^d \sum_{x \in \Lambda_a} {:}P(\phi(x)){:}_{c_a}$$

and the partition function normalizes to a probability measure:

$$Z_a = \int e^{-V_a(\phi)}\, d\mu_{\mathrm{GFF}}(\phi).$$

### Well-definedness

The measure $\mu_a$ is well-defined because of two properties of the
Wick-ordered interaction:

**1. Bounded below.** Since ${:}P(\tau){:}_c$ is a monic even polynomial
of degree $n \geq 4$ in $\tau$ (with positive leading coefficient $1/n$),
it is bounded below for each fixed $c$:

$${:}P(\tau){:}_c \geq -A(c) \qquad \text{for all } \tau \in \mathbb{R}.$$

This means $V_a(\phi) \geq -a^d |\Lambda| A(c_a)$, so $e^{-V_a}$ is bounded
above and the Boltzmann weight is integrable against $\mu_{\mathrm{GFF}}$.
The constant $A$ depends on $c$, but the uniform bound $c_a \leq 1/m^2$
ensures that $A(c_a)$ stays bounded as $a \to 0$. This is proved as
`wickPolynomial_bounded_below` and lifted to the lattice level in
`latticeInteraction_bounded_below`.

**2. Positive partition function.** Since $e^{-V_a} > 0$ everywhere and
$\mu_{\mathrm{GFF}}$ is a probability measure, the integral $Z_a$ is
strictly positive (`partitionFunction_pos`). Therefore the density
$e^{-V_a}/Z_a$ is well-defined.

**3. Jensen's inequality: $Z_a \geq 1$.** By convexity of the exponential,

$$Z_a = \int e^{-V_a}\, d\mu_{\mathrm{GFF}} \geq \exp\!\left(-\int V_a\, d\mu_{\mathrm{GFF}}\right).$$

The Hermite orthogonality property gives $\int {:}\tau^n{:}_{c_a}\, d\mu_{\mathrm{GFF}} = 0$
for $n \geq 1$, so

$$\int V_a\, d\mu_{\mathrm{GFF}} = a^d |\Lambda| \cdot P.\mathrm{coeff}_0 \leq 0$$

(the constant coefficient is nonpositive by convention). Therefore
$Z_a \geq e^0 = 1$. This bound `partitionFunction_ge_one` is crucial for the
Cauchy--Schwarz density transfer that underpins hypercontractivity.

### Single-site structure

The interaction $V_a(\phi) = a^d \sum_x v(\phi(x))$ is a sum of **single-site
functions**: each term depends on $\phi$ only through the value $\phi(x)$ at
one lattice site. This factored structure is what enables the FKG inequality
via `fkg_perturbed` from the `gaussian-field` library. Note that FKG does not
require convexity of $V_a$ (which would fail for typical interactions like
$\tau^4 - \mu \tau^2$) -- only the single-site decomposition matters.

## Formalization Details

The Wick ordering infrastructure is spread across three files:

| File | Contents | Status |
|------|----------|--------|
| `Pphi2/WickOrdering/WickPolynomial.lean` | `wickMonomial`, `wickPolynomial`, bounded below, connection to Hermite polynomials | Fully proved |
| `Pphi2/WickOrdering/Counterterm.lean` | `wickConstant`, positivity, upper bound $c_a \leq 1/m^2$, monotonicity in mass | Fully proved |
| `Pphi2/InteractingMeasure/LatticeAction.lean` | `latticeInteraction`, bounded below, continuity, single-site structure | Fully proved |
| `Pphi2/InteractingMeasure/LatticeMeasure.lean` | `interactionFunctional`, `partitionFunction`, `interactingLatticeMeasure`, measurability | Fully proved |

Key theorems:

- `wickMonomial_eq_hermite` -- Wick monomials equal scaled Hermite polynomials (for $c > 0$).
- `wickPolynomial_bounded_below` -- Even-degree Wick polynomials are bounded below.
- `wickConstant_pos` -- The Wick constant is positive when $m > 0$.
- `wickConstant_le_inv_mass_sq` -- Uniform upper bound $c_a \leq 1/m^2$.
- `partitionFunction_pos` -- The partition function is strictly positive.
- `partitionFunction_ge_one` -- Jensen's inequality: $Z_a \geq 1$.
- `latticeInteraction_single_site` -- The interaction decomposes as a sum of single-site functions.

All theorems in the Wick ordering and interacting measure modules are fully
proved (0 axioms, 0 sorries).

## References

- Simon, B., *The P(Phi)_2 Euclidean (Quantum) Field Theory*, Princeton
  University Press, 1974, Ch. I (Wick ordering), Ch. II (interacting measure).
- Glimm, J. and Jaffe, A., *Quantum Physics: A Functional Integral Point
  of View*, 2nd ed., Springer, 1987, Section 8.6.
- Nelson, E., "Construction of quantum fields from Markoff fields," *J. Funct.
  Anal.* **12** (1973), 97--112.
