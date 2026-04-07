# Reflection Positivity in the P(Phi)_2 Construction

## What Reflection Positivity Means

Reflection positivity (RP) is a positivity condition on a Euclidean field
theory measure $\mu$ with respect to time reflection. In two-dimensional
Euclidean spacetime $\mathbb{R}^2$ with coordinates $(t, x)$, the time
reflection is the involution

$$\Theta : (t, x) \mapsto (-t, x).$$

Given a probability measure $\mu$ on the space of distributions
$\mathcal{S}'(\mathbb{R}^2)$, we define the generating functional

$$Z[f] = \int_{\mathcal{S}'(\mathbb{R}^2)} e^{i \langle \omega, f \rangle} \, d\mu(\omega)$$

for real Schwartz test functions $f \in \mathcal{S}(\mathbb{R}^2)$. The
time reflection acts on test functions by pullback: $(\Theta f)(t,x) = f(-t,x)$.

**The RP condition (OS3)** states: for any finite collection of test functions
$f_1, \ldots, f_n$ supported at strictly positive times $t > 0$, and any
real coefficients $c_1, \ldots, c_n$,

$$\sum_{i,j} c_i \, c_j \, \operatorname{Re} Z[f_i - \Theta f_j] \geq 0.$$

In other words, the $n \times n$ matrix with entries
$M_{ij} = \operatorname{Re} Z[f_i - \Theta f_j]$ is positive semidefinite.

Informally: reflecting through the $t = 0$ hyperplane and correlating
with the original produces a positive inner product. This is the Euclidean
shadow of unitarity.

## Why It Matters: The OS Reconstruction Theorem

Reflection positivity is the bridge between Euclidean statistical mechanics
and Minkowski quantum field theory. Without it, a Euclidean measure is
merely a classical statistical system; with it, the measure encodes a
genuine quantum theory.

The **Osterwalder-Schrader reconstruction theorem** (1973, 1975) states that
a probability measure $\mu$ on $\mathcal{S}'(\mathbb{R}^d)$ satisfying
axioms OS0--OS4 determines a Wightman quantum field theory in $(d-1)+1$
dimensional Minkowski spacetime satisfying all Wightman axioms: Poincare
covariance, positive-definiteness of the metric (unitarity), the spectral
condition, and locality.

Each OS axiom has a specific role in this reconstruction:

| Axiom | Euclidean property | Minkowski consequence |
|-------|-------------------|----------------------|
| OS0 (Analyticity) | $Z[\sum z_i f_i]$ entire in $z \in \mathbb{C}^n$ | Temperedness of Wightman distributions |
| OS1 (Regularity) | Exponential bounds on $Z$ | Growth conditions for distributions |
| OS2 (Euclidean invariance) | $Z[g \cdot f] = Z[f]$ for $g \in E(d)$ | Poincare covariance |
| **OS3 (Reflection positivity)** | **RP matrix $\geq 0$** | **Positive-definite Hilbert space metric** |
| OS4 (Clustering) | Factorization at large distances | Uniqueness of the vacuum |

The reconstruction works as follows. The RP condition provides a positive
semidefinite sesquilinear form on the space of positive-time functionals.
Quotienting by the null space and completing gives the physical Hilbert
space $\mathcal{H}$. Time translations $t \geq 0$ become a contraction
semigroup $e^{-tH}$ on $\mathcal{H}$ by the Markov property, and the
Hamiltonian $H \geq 0$ follows from the spectral condition. Analytic
continuation from Euclidean (imaginary) time to real Minkowski time is
then achieved via the Osterwalder-Schrader construction.

Without RP, one cannot define a positive-definite inner product on the
physical state space, and the entire reconstruction collapses. The
Euclidean measure would describe a perfectly valid statistical mechanics
system, but it would not correspond to any quantum theory.

## The Perfect Square Argument on the Lattice

The proof of RP on a finite lattice is one of the most elegant arguments
in constructive QFT. It reduces the positivity condition to the elementary
fact that a perfect square is nonneg.

### Setup

Consider a square $N \times N$ lattice with sites
$(t, x) \in \mathbb{Z}/N\mathbb{Z} \times \mathbb{Z}/N\mathbb{Z}$.
The time reflection is $\Theta(t, x) = (-t, x)$, computed modulo $N$.

**Step 1: Decompose the field.** Partition the lattice sites into three
regions based on the time coordinate:

- $S_+ = \{(t, x) : 0 < t < N/2\}$ (positive-time sites),
- $S_0 = \{(t, x) : t = 0 \text{ or } t = N/2\}$ (boundary sites),
- $S_- = \Theta(S_+) = \{(t, x) : N/2 < t < N\}$ (negative-time sites).

The field configuration $\phi$ decomposes accordingly:
$\phi = (\phi_+, \phi_0, \phi_-)$ where $\phi_\pm$ are the restrictions
to $S_\pm$ and $\phi_0$ is the restriction to $S_0$.

**Step 2: The action splits.** The nearest-neighbor lattice action
$S[\phi]$ involves couplings only between adjacent time slices. Because
the coupling structure is symmetric under $\Theta$, the action decomposes:

$$S[\phi] = S_+[\phi_+, \phi_0] + S_+[\Theta\phi_-, \phi_0]$$

where $S_+$ depends only on the positive-time and boundary fields. The
key identity is $S_-[\phi_-, \phi_0] = S_+[\Theta\phi_-, \phi_0]$:
the negative-time action on $\phi_-$ equals the positive-time action
on the reflected field.

In the formalization, this is `action_decomposition` in
`Pphi2/OSProofs/OS3_RP_Lattice.lean`. The proof uses the fact that the
Wick interaction $V = a^2 \sum_x {:}P(\phi(x)){:}$ is a single-site sum,
so reindexing via the reflection bijection $\Theta : S_- \to S_+$ maps
$V_- \mapsto V_+$.

**Step 3: The perfect square.** For any functional $F$ supported at positive
times:

$$\int F(\phi) \, \overline{F(\Theta\phi)} \, d\mu
  = \frac{1}{Z} \int d\phi_0 \left[ \int F(\phi_+, \phi_0) \, e^{-S_+[\phi_+, \phi_0]} \, d\phi_+ \right]^2
  \geq 0.$$

The square appears because the $\phi_-$ integration, after the change of
variables $\phi_- \mapsto \Theta\phi_-$, becomes identical to the $\phi_+$
integration. Since $\overline{F(\Theta\phi)} = F(\Theta\phi_-)$ when $F$
depends only on positive-time fields, and $S_-[\phi_-] = S_+[\Theta\phi_-]$,
both halves produce the same integral over their respective half-spaces.
The product of two identical integrals is a perfect square, hence nonneg.

This argument is formalized in `lattice_rp_matrix` in `OS3_RP_Lattice.lean`.

## Connection to the Transfer Matrix

The perfect square structure of RP is intimately connected to the transfer
matrix formalism. The transfer matrix $T$ is the integral operator that
propagates the field one time step:

$$(T\psi)(\phi_0) = \int e^{-S_{\text{one-step}}[\phi_1, \phi_0]} \, \psi(\phi_1) \, d\phi_1.$$

The action decomposition $S = S_+ + S_+(\Theta \cdot)$ corresponds to
factoring the partition function through the boundary:

$$Z = \int d\phi_0 \, (T^{N/2} \mathbf{1})(\phi_0) \cdot (T^{N/2} \mathbf{1})(\phi_0)$$

which is manifestly a perfect square (an $L^2$ inner product of
$T^{N/2}\mathbf{1}$ with itself).

More precisely, RP is equivalent to the statement that $T$ has nonneg
eigenvalues. This follows because $T$ itself can be factored as
$T = M_w \circ \text{Conv}_G \circ M_w$, where $M_w$ is multiplication
by a nonneg weight and $\text{Conv}_G$ is convolution with a Gaussian
kernel. Thus $T = A^* A$ for an appropriate "half-transfer" operator $A$,
which forces all eigenvalues to be nonneg. This factorization is central
to the Perron-Frobenius/Jentzsch analysis in the project
(`Pphi2/TransferMatrix/`), where the positivity-improving property of $T$
implies a simple ground state with a spectral gap.

## Preservation Under Weak Limits

A crucial property of RP is that it survives the continuum limit. This
is the content of `rp_closed_under_weak_limit` in
`Pphi2/OSProofs/OS3_RP_Inheritance.lean`.

**Theorem.** If $\{\mu_n\}$ is a sequence of RP measures on a topological
space $X$ equipped with a continuous reflection $\Theta$, and
$\mu_n \rightharpoonup \mu$ weakly, then $\mu$ is RP.

**Proof.** The argument is purely topological and does not depend on any
details of the field theory.

1. For any bounded continuous function $F$, the composite
   $x \mapsto F(x) \cdot F(\Theta x)$ is also bounded continuous (since
   $\Theta$ is continuous).

2. Weak convergence means $\int F(x) \cdot F(\Theta x) \, d\mu_n \to
   \int F(x) \cdot F(\Theta x) \, d\mu$ for each such $F$.

3. Each term $\int F \cdot (F \circ \Theta) \, d\mu_n \geq 0$ by the RP
   hypothesis on $\mu_n$.

4. A limit of nonneg real numbers is nonneg.

In the formalization, this is a clean four-line proof:

```
exact ge_of_tendsto h_tend (.of_forall (fun n => h_rp n F hF))
```

The bounded continuous test functions $\phi \mapsto e^{i\langle\phi,f\rangle}$
appearing in the generating functional form of RP are indeed bounded
(by 1 in absolute value) and continuous on $\mathcal{S}'(\mathbb{R}^2)$
in the weak-$*$ topology. So the lattice RP transfers to the continuum
limit without any additional work.

This is one of the cleanest parts of the entire construction: the
formalization of `continuum_rp_from_lattice` is a direct corollary of
`rp_closed_under_weak_limit`, with zero axioms required.

## The Generating Functional Form

In the formalization (`Pphi2/OSAxioms.lean`), OS3 is stated via the
generating functional rather than via Schwinger $n$-point functions.
The formal definition is:

```lean
def OS3_ReflectionPositivity
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ] : Prop :=
  ∀ (n : ℕ) (f : Fin n → PositiveTimeTestFunction2) (c : Fin n → ℝ),
    0 ≤ ∑ i, ∑ j, c i * c j *
      (generatingFunctional μ
        ((f i).val - compTimeReflection2 ((f j).val))).re
```

Here `PositiveTimeTestFunction2` is the type of Schwartz functions
$f \in \mathcal{S}(\mathbb{R}^2)$ whose topological support is contained
in the positive-time half-space $\{(t,x) : t > 0\}$, and
`compTimeReflection2` implements the pullback $f \mapsto f \circ \Theta$.

The matrix entry $\operatorname{Re} Z[f_i - \Theta f_j]$ can be expanded:

$$\operatorname{Re} Z[f_i - \Theta f_j]
  = \operatorname{Re} \int e^{i\langle\omega, f_i - \Theta f_j\rangle} \, d\mu
  = \int \cos(\langle\omega, f_i\rangle - \langle\omega, \Theta f_j\rangle) \, d\mu.$$

This is equivalent to the Schwinger function formulation via formal
expansion of the exponential: if we write
$e^{i\langle\omega,f\rangle} = \sum_n (i^n/n!) \langle\omega,f\rangle^n$,
the RP matrix condition for the generating functional implies RP for
all $n$-point Schwinger functions $S_n(x_1,\ldots,x_n) =
\int \omega(x_1)\cdots\omega(x_n) \, d\mu(\omega)$, and conversely.
The generating functional form is more convenient for the formalization
because it avoids distributional products.

## Formalization Status

Reflection positivity in this project follows two routes:

**Lattice RP (OS3_RP_Lattice.lean).** The perfect square argument is
proved for the torus lattice $(\mathbb{Z}/N\mathbb{Z})^2$. The key
ingredients are:

- `siteEquiv`: equivalence between the product representation
  $\mathbb{Z}/N\mathbb{Z} \times \mathbb{Z}/N\mathbb{Z}$ and the
  function representation `FinLatticeSites 2 N` used by the gaussian-field
  library.
- `timeReflection2D`: the lattice reflection $\Theta(t,x) = (-t, x)$,
  proved to be an involution.
- `PositiveTimeSupported`: predicate for functionals depending only on
  field values at times $0 < t < N/2$.
- `action_decomposition`: the action splitting $S[\phi] = S_+[\phi] +
  S_+[\Theta\phi]$, proved by reindexing the site sum via the
  reflection bijection.
- `lattice_rp_matrix`: the RP inequality on the lattice.

**Weak limit inheritance (OS3_RP_Inheritance.lean).** The abstract
theorem `rp_closed_under_weak_limit` is fully proved with zero axioms.
It applies to any topological space with a continuous involution, making
it reusable beyond the P(Phi)_2 setting. The corollary
`continuum_rp_from_lattice` specializes to the lattice-to-continuum
transfer.

The cylinder route (Route B' in the project) provides a particularly
clean RP because the time reflection $t \mapsto -t$ is a natural
involution on $S^1 \times \mathbb{R}$, where the periodic time direction
eliminates boundary effects at infinity.

## References

- K. Osterwalder and R. Schrader, "Axioms for Euclidean Green's functions,"
  *Comm. Math. Phys.* **31** (1973), 83--112.
- K. Osterwalder and R. Schrader, "Axioms for Euclidean Green's functions II,"
  *Comm. Math. Phys.* **42** (1975), 281--305.
- J. Glimm and A. Jaffe, *Quantum Physics: A Functional Integral Point of View*,
  Springer, 1987, Ch. 6 (reflection positivity) and Ch. 19 (lattice construction).
- B. Simon, *The P(phi)_2 Euclidean (Quantum) Field Theory*, Princeton, 1974,
  Ch. III (Osterwalder-Schrader axioms and reconstruction).
- K. Osterwalder and E. Seiler, "Gauge field theories on a lattice,"
  *Ann. Physics* **110** (1978), 440--471 (lattice RP).
