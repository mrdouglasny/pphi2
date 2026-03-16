# Nelson's Exponential Estimate — Proof Documentation

## Statement

For the P(phi)_2 lattice theory on the 2D torus T^2_L with lattice spacing
a = L/N and mass m > 0:

```
integral exp(-2V) d mu_GFF <= K
```

where K depends on the interaction polynomial P, the torus size L, and the
mass m, but **NOT** on the lattice size N.

**Lean theorem:** `nelson_exponential_estimate_lattice` in
`Pphi2/NelsonEstimate/NelsonEstimate.lean`.

## The Key Insight

The naive bound gives K = exp(2 * N^2 * A), which blows up as N -> infinity.
The correct bound uses the physical volume identity:

```
a^2 * N^2 = (L/N)^2 * N^2 = L^2
```

Since the interaction functional is `V(omega) = a^2 * sum_x :P(phi(x)):_c`,
and the Wick polynomial is bounded below by `-A` per site
(from `wickPolynomial_uniform_bounded_below`), we get:

```
V(omega) >= -a^2 * N^2 * A = -L^2 * A
```

Therefore `exp(-2V) <= exp(2 * L^2 * A)`, and since the GFF measure is a
probability measure:

```
integral exp(-2V) d mu_GFF <= exp(2 * L^2 * A) = K
```

This K depends on L and A (which depends on P and mass) but **not on N**.

## Why the Wick Constant Doesn't Blow Up

The lower bound constant A comes from `wickPolynomial_uniform_bounded_below P c_max`,
where `c_max = mass^{-2}`. The Wick constant c_a satisfies `c_a <= mass^{-2}`
uniformly in N (proved in `wickConstant_le_inv_mass_sq`). So A depends only on
P and mass, not on N.

## Module Structure

The proof infrastructure in `Pphi2/NelsonEstimate/` (6 files, ~600 lines):

### CovarianceSplit.lean (0 sorries)
- `smoothCovEigenvalue`, `roughCovEigenvalue` — heat kernel covariance splitting
- `covariance_split` — C(k) = C_S(k) + C_R(k)
- `wickConstant_split` — c_a = c_S + c_R
- `roughCovEigenvalue_le_T` — C_R(k) <= T (from 1 - exp(-x) <= x)
- `smoothVariance_le_log` — c_S <= C * (1 + |log T|)
- `roughCovariance_sq_summable` — sum C_R(k)^2 <= T * wickConstant

### HeatKernelBound.lean (0 sorries)
- `hasDerivAt_neg_exp_div` — d/dt[-exp(-t*lambda)/lambda] = exp(-t*lambda)
- `schwinger_smooth_Ioi` — integral_Ioi exp(-t*lambda) = exp(-T*lambda)/lambda
- `schwinger_rough_interval` — integral_0^T exp(-t*lambda) = (1-exp(-T*lambda))/lambda
- `sin_sq_lower_bound` — Jordan's inequality: sin^2(x) >= (2/pi)^2 * x^2
- `gaussian_sum_bound` — sum exp(-alpha*k^2) <= 1 + sqrt(pi/alpha)
- `heat_kernel_1d_bound`, `heat_kernel_trace_bound` — H(t) <= C/t
- `smoothVariance_from_heat_kernel`, `roughVariance_from_heat_kernel`

### WickBinomial.lean (1 sorry — unused general case)
- `wickMonomial_two_add` — Wick binomial for n=2
- `wickMonomial_four_add` — Wick binomial for n=4 (phi^4 theory)
- `wickMonomial_four_lower_bound` — :x^4:_c >= -6c^2

### SmoothLowerBound.lean (0 sorries)
- `site_interaction_lower_bound` — per-site bound
- `smooth_interaction_lower_bound` — sum over lattice
- `smooth_interaction_lower_bound_volume` — volume-independent (a^2*N^2 = L^2)
- `smooth_interaction_lower_bound_log` — V_S >= -C*(1+|log T|)^2

### RoughErrorBound.lean (placeholder)
- Documentation of the hypercontractivity approach for optimal bounds
- Not needed for the basic proof (physical volume argument suffices)

### NelsonEstimate.lean (0 sorries)
- `nelson_exponential_estimate_lattice` — THE MAIN THEOREM

## Historical Context

Nelson's original estimate (1966) used a deep argument involving
covariance splitting and hypercontractivity to get the OPTIMAL bound.
The heat kernel splitting infrastructure in this module (Schwinger
parametrization, Jordan's inequality, Gaussian sum bounds, trace bounds)
was developed for that approach.

However, the key insight for the lattice torus setting is simpler:
the physical volume `a^2 * N^2 = L^2` is CONSTANT in N, so the naive
pointwise bound on the Wick polynomial already gives a uniform-in-N
bound. The covariance splitting machinery is available for the
optimal-constant version or for the infinite-volume limit (Route A).

## References

- Nelson (1966), "A quartic interaction in two dimensions"
- Simon, *The P(phi)_2 Euclidean (Quantum) Field Theory*, Chapter V
- Glimm-Jaffe, *Quantum Physics*, Section 8.6
