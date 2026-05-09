# Dual-Construction Strategy for OS2 + OS3

> **Status:** Strategic-design document. The current pphi2 main path uses the
> single-construction (lattice + Ward-identity) plan. This document records
> the alternative dual-construction strategy as a backup route and as a
> conceptual reference, including what would have to be done to execute it.

## Statement of the strategy

The two Osterwalder-Schrader axioms `OS2` (full $E(2) = \mathbb{R}^2 \rtimes O(2)$
Euclidean invariance) and `OS3` (reflection positivity) trade off cleanly
against the choice of UV regulator:

* A **lattice** regulator gives `OS3` for free (transfer-matrix positivity for
  nearest-neighbour actions on a slice plane), but breaks $E(2)$ to the
  hypercubic point group — full $O(2)$ has to be recovered by a Ward-identity
  argument in the continuum limit.
* A **Euclidean-invariant** regulator (heat kernel, momentum cutoff,
  rotational mollification) gives `OS2` for free, but does not in general
  preserve `OS3` at the regulator level (the smoothing kernel smears across
  the $t = 0$ plane, breaking the time-zero factorisation that powers the
  transfer matrix).

The strategy is to construct two interacting measures — one with each
regulator — show that **both converge to the same limit**, and read off
both axioms from whichever construction makes them obvious.

```
   Construction A                          Construction B
(heat-kernel regulator)                   (lattice regulator)
        │                                          │
        │  E(2)-invariant at every t > 0           │  RP at every a > 0
        ▼                                          ▼
  μ_A on S'(ℝ²)        ───── matching ─────►  μ_B on S'(ℝ²)
        │                                          │
   inherits OS2                              inherits OS3
        └─────────────────── μ ───────────────────┘
                       inherits OS2 + OS3
```

## Constructions

### Construction A: Euclidean-invariant regulator

Three standard candidates, all $E(2)$-invariant:

1. **Heat-kernel UV cutoff.** Replace $\phi$ by $\phi_t := e^{-tH}\phi$
   where $H = -\Delta + m^2$. The smoothed field $\phi_t$ is a smooth
   function on $\mathbb{R}^2$, so $:P(\phi_t):_{c_t}$ with the matched
   Wick constant $c_t = G_t(0,0) = \int K_t(x,x)\,dx \;/\;\text{vol}$
   makes pointwise sense. Take $t \to 0$.

2. **Sharp / smooth momentum cutoff.** Replace the Gaussian covariance
   $C(k) = (k^2 + m^2)^{-1}$ by $C_\Lambda(k) = \chi(|k|/\Lambda) \cdot C(k)$
   for a rotationally-symmetric profile $\chi$. Take $\Lambda \to \infty$.

3. **Mollification.** Convolve test functions with a rotationally-symmetric
   mollifier $\rho_\epsilon$ before pairing. Take $\epsilon \to 0$.

For each, the regulated interacting measure is
$$ \mu_t \;=\; \frac{1}{Z_t}\, e^{-V_t[\phi]}\, d\mu_{\text{GFF}}, \qquad V_t = \int_{\mathbb{R}^2} :P(\phi_t):_{c_t}\, dx, $$
and is $E(2)$-invariant by construction (every ingredient — $H$, $\rho_\epsilon$,
$dx$, the Wick subtraction $c_t$ — is $E(2)$-invariant).

**`OS2`-invariance is automatic** for $\mu_t$ at every $t > 0$, and is
preserved under any reasonable weak limit $t \to 0$.

**`OS3` is _not_ automatic** for $\mu_t$ — the smoothing kernel $K_t(x, y)$
extends across $\{t = 0\}$, so the action does not factor through that
plane and the transfer-matrix argument does not run. You can sometimes
recover `OS3` *in the limit* if it shows up as a positivity property of
the limiting Schwinger functions, but not at finite $t$.

### Construction B: Lattice regulator

This is what pphi2 currently builds (Routes A / B / B′). The regulated
measure is
$$ \mu_a \;=\; \frac{1}{Z_a}\, e^{-V_a[\phi]}\, \mu_{\text{GFF},a}, \qquad V_a(\phi) = a^2 \sum_{x \in (\mathbb{Z}/N\mathbb{Z})^2} :P(\phi(x)):_{c_a}, $$
on the finite lattice with spacing $a = L/N$.

**`OS3` is automatic** at every $a > 0$ via the Osterwalder-Schrader
transfer-matrix argument: the nearest-neighbour kinetic term factors through
any time-zero slice $\{t = 0\}$, the slice spin variables form a separating
finite-dimensional algebra, and the Markov property gives the RP matrix
positive semidefiniteness. Inheritance to the continuum limit is by
`rp_closed_under_weak_limit` — already in `OSProofs/OS3_RP_Inheritance.lean`.

**`OS2` is _not_ automatic** — only the discrete subgroup of lattice
translations and the hypercubic point group $D_4$ are exact symmetries
at finite $a$. Full $O(2)$ has to be recovered.

## The matching theorem

The dual-construction strategy hinges on showing
$$ \mu_A \;=\; \mu_B \quad \text{as measures on } \mathcal{S}'(\mathbb{R}^2). $$
Two centred Radon probability measures on $\mathcal{S}'(\mathbb{R}^2)$
agree iff their characteristic functionals agree on a separating dense
subspace of $\mathcal{S}(\mathbb{R}^2)$:
$$ \int_{\mathcal{S}'} e^{i\langle\omega, f\rangle}\, d\mu_A(\omega) \;=\; \int_{\mathcal{S}'} e^{i\langle\omega, f\rangle}\, d\mu_B(\omega) \quad \forall f \in \mathcal{D}. $$
So the matching reduces to
$$ \boxed{\;\lim_{t \to 0}\, Z_t^{\text{heat}}[f] \;=\; \lim_{a \to 0}\, Z_a^{\text{lattice}}[f] \quad \forall f \in \mathcal{S}(\mathbb{R}^2).\;}$$

There are essentially four routes to prove this. Each is itself a
substantial body of mathematics.

### Route 1: convergent perturbation / cluster expansion

Expand both $Z_t^{\text{heat}}$ and $Z_a^{\text{lattice}}$ as power series
in the coupling $\lambda$ after Wick subtraction. For super-renormalizable
$P(\Phi)_2$, the series converges in a $\lambda$-neighbourhood of $0$
uniformly in the regulator. Both series have identical Feynman-diagram
coefficients in the appropriate limit (renormalisation conditions match
because both schemes use the same propagator $(-\Delta + m^2)^{-1}$ up
to bounded perturbation). Cluster / Mayer / polymer expansion techniques
prove convergence and identify the limits.

This is the **Glimm-Jaffe / Brydges-Federbush** approach. Heaviest in
combinatorics; ~thousands of lines of Lean.

References: Glimm-Jaffe, *Quantum Physics*, §8; Brydges, *A Short
Course on Cluster Expansions* (Les Houches 1984).

### Route 2: moment-problem matching

If both schemes give identical Schwinger functions
$$ S_n(f_1, \ldots, f_n) = \int \langle\omega, f_1\rangle\cdots\langle\omega, f_n\rangle \, d\mu(\omega) $$
to all orders, **and** the moments satisfy a Carleman / Hamburger
uniqueness condition, then $\mu_A = \mu_B$.

For $P(\Phi)_2$, Nelson's exponential bounds give moment growth
$|S_n(f_1,\ldots,f_n)| \le C^n n^{n/2}\,\prod\|f_i\|$, which is
strictly subexponential in $n$ for a fixed test-function sequence —
enough for Carleman uniqueness to apply.

The moment-matching itself is again proved via cluster expansion (or
direct computation in low orders + induction). Conceptually clean but
in practice nearly identical work to Route 1.

References: Reed-Simon vol. 2 §X.6 (moment problem); Glimm-Jaffe §8.6.

### Route 3: stochastic-quantization identification

Both regulator schemes can be lifted to stationary Markovian dynamics
(Parisi-Wu stochastic quantisation): a parabolic SPDE
$$ \partial_\tau \phi \;=\; (\Delta - m^2)\phi \;-\; P'(\phi) \;+\; \sqrt{2}\,\xi, \qquad \xi = \text{space-time white noise}, $$
with the appropriate UV cutoff. The interacting measure is the unique
stationary distribution. As the regulator is removed, the SPDEs converge
in some sense (e.g. in regularity-structures topology), and uniqueness
of the limiting invariant measure forces $\mu_A = \mu_B$.

Modern (Hairer's regularity structures, Gubinelli-Imkeller-Perkowski
paracontrolled distributions) but very heavy machinery — currently
unsuitable for Lean formalisation in any reasonable timescale.

References: Da Prato-Debussche, *Strong solutions to the stochastic
quantization equations* (2003); Hairer-Mourrat-Weber, *The dynamic
$\Phi^4_3$ model* (2017).

### Route 4: direct semigroup matching via Trotter-Kato

The lattice transfer matrix $T_a = e^{-aH_a}$ defines a discrete-time
semigroup whose continuum limit is $e^{-tH}$ for some self-adjoint
Hamiltonian $H$ on a Hilbert space. The heat-kernel-regularised
construction defines a continuous-time semigroup directly. If both
semigroups have the same generator $H$ (modulo conjugation by an
isometry), they generate the same Markov process, hence the same
invariant measure.

This needs:

1. Uniform spectral-gap and norm-resolvent bounds on $T_a$.
2. Self-adjoint extension theory for the formal generator $-\Delta + m^2 + P'(\phi)$
   in the heat-kernel construction.
3. Trotter-Kato semigroup convergence.

Cleanest abstractly; the ingredients are textbook (Reed-Simon vol. 1
chapter VIII) but each one is its own substantial Lean development.

References: Reed-Simon vol. 1 §VIII.7; Faris-Simon, *Degenerate and
non-degenerate ground states for Schrödinger operators* (1975).

## Cost comparison versus the current single-construction plan

### Current plan (lattice + Ward identity)

Status:
* `OS3`: lattice transfer-matrix positivity is proved; weak-limit
  inheritance (`rp_closed_under_weak_limit`) is essentially a Mathlib
  exercise. **~done.**
* `OS2` translations: lattice approximation argument
  (`docs/translation-invariance-proof.md`) — Steps 1-5 are largely
  proved; the residual Cauchy-Schwarz transfer to interacting moments
  is a clean local job. **~weeks.**
* `OS2` rotations: Ward identity + anomaly bound
  $O(a^2 |\log a|^p)$, current axiom slot
  `rotation_cf_defect_polylog_bound` in
  `Pphi2/OSProofs/OS2_WardIdentity.lean`. The bound is the standard
  Symanzik / Lüscher-Weisz polylog estimate from
  Glimm-Jaffe Ch. 19 / Symanzik (1983) /
  Lüscher-Weisz (1985). **~weeks (single isolated estimate).**

Total residual to close `OS2 + OS3` on the current plan: low single-digit
months.

### Dual-construction plan

Cost:
* Build Construction A (heat-kernel regularised P(φ)₂):
  define the regulated measure, prove tightness, prove convergence as
  $t \to 0$. **~3-6 months** (it's a complete second construction,
  comparable in scope to Route B′ already in pphi2).
* Prove `OS2` for $\mu_A$ and inheritance to the limit. **~weeks.**
* Prove the matching theorem $\mu_A = \mu_B$ via one of Routes 1-4.
  Route 1 (cluster expansion) and Route 2 (moments) are the most
  tractable for Lean; Route 3 (stochastic quantisation) is currently
  out of reach; Route 4 (Trotter-Kato) is appealing but needs heavy
  spectral theory. **~6-12 months.**

Total: 9-18 months, with a strong dependence on which matching route is
chosen.

## Recommendation

**Stay with the lattice + Ward-identity plan as the primary route.** It
has the lowest remaining cost and the OS3 side is essentially in place.
The polylog rotation-anomaly bound is a textbook estimate, well-isolated,
and doesn't require building a parallel construction.

The dual-construction plan is worth keeping in mind:

* As a **fallback** if the polylog bound turns out to be harder than
  expected to formalise.
* As a future **independent verification** — proving the same theorem
  by two genuinely different routes is a strong sanity check.
* The heat-kernel construction (Construction A) has standalone value
  beyond just delivering OS2: it is the natural continuum perturbative
  framework, gives access to renormalisation-group flow results, and
  feeds directly into stochastic-quantisation work.

If priorities shift and dual-construction becomes the active plan,
**Route 2 (moment matching)** is the recommended matching strategy:
the moment growth bound from Nelson's hypercontractive estimate is
already formalised (`GaussianField/HypercontractiveNat.lean`), and
matching low-order moments + Carleman uniqueness is more tractable
in Lean than full cluster-expansion convergence.

## References

* J. Glimm and A. Jaffe, *Quantum Physics: A Functional Integral Point
  of View*, 2nd ed., Springer (1987) — Chs. 8, 19. The classical lattice
  + Ward-identity treatment.
* B. Simon, *The P(φ)₂ Euclidean (Quantum) Field Theory*, Princeton
  (1974) — both lattice and continuum constructions, Markov property
  for OS3.
* K. Symanzik, "Continuum limit and improved action in lattice
  theories", Nucl. Phys. B226 (1983).
* M. Lüscher and P. Weisz, "On-shell improved lattice gauge theories",
  Comm. Math. Phys. 97 (1985).
* D. Brydges, *A Short Course on Cluster Expansions*, Les Houches (1984)
  — the cluster-expansion route to matching.
* G. Da Prato and A. Debussche, "Strong solutions for the stochastic
  quantization equations", Ann. Probab. 31 (2003) — stochastic
  quantisation route.
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics* vol. 1
  §VIII.7 (Trotter-Kato) and vol. 2 §X.6 (moment problem).
