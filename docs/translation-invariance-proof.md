# Translation Invariance of the Interacting Continuum Limit

## Statement

For the weak limit measure `mu_P` of the torus interacting P(phi)_2 theory:

  Z[T_v f] = Z[f]  for all v in R^2, f in TestFunctions

where `Z[f] = integral exp(i omega(f)) d mu_P` is the generating functional
and `T_v` is translation by v on the torus T^2_L = (R/LZ)^2.

## Why This is Non-Trivial

At finite cutoff N, the lattice interacting measure is only invariant under
**lattice translations** (multiples of the lattice spacing a = L/N). For a
general v in R^2, Z_N[T_v f] != Z_N[f] because the torus embedding evaluates
test functions at lattice points, and non-lattice translations shift these
evaluation points off the grid.

Translation invariance for all v is a property of the **continuum limit**.

## Proof Strategy

### Step 1: Lattice Translation Invariance (Axiom)

At each cutoff N, Z_N[T_w f] = Z_N[f] for lattice vectors w = (j*a, k*a)
where j, k in Z and a = L/N. This follows from `latticeMeasure_translation_invariant`:
the interaction V sums over all lattice sites (relabeling-invariant), the GFF
covariance is translation-invariant, and Lebesgue measure is preserved.

### Step 2: The Approximation Argument

For any v in R^2, choose lattice approximations w_n = (a_n * round(v.1/a_n), ...)
where a_n = L/(phi(n)+1) -> 0. Then |v - w_n| <= a_n * sqrt(2) / 2 -> 0.

**Key bound** (using |exp(ix) - exp(iy)| <= |x - y|):

  |Z_N[T_v f] - Z_N[T_{w_n} f]| <= E_P[|omega(T_v f - T_{w_n} f)|]
                                   <= sqrt(E_P[(omega(h_n))^2])

where h_n = T_v f - T_{w_n} f.

### Step 3: Interacting-to-Gaussian Bridge (Axiom 2)

The second moment of omega(h) under the interacting measure is controlled
by the Gaussian second moment:

  E_P[(omega(h))^2] <= C * E_GFF[(omega(h))^2] = C * G_N(h, h)

This follows from Cauchy-Schwarz density transfer:
  E_P[F] = (1/Z) E_GFF[F * exp(-V)]
         <= (1/Z) sqrt(E_GFF[F^2]) sqrt(E_GFF[exp(-2V)])
         <= sqrt(K) sqrt(E_GFF[F^2])

Applied to F = (omega(h))^2 with Gaussian hypercontractivity E[X^4] = 3(E[X^2])^2:
  E_P[(omega(h))^2] <= sqrt(K) sqrt(3) E_GFF[(omega(h))^2] = sqrt(3K) G_N(h, h)

The constant C = sqrt(3K) is **universal** (independent of h and N).

### Step 4: Gaussian Green's Function Continuity

G_N(h_n, h_n) -> 0 because:

  G_N(T_v f - T_{w_n} f, T_v f - T_{w_n} f)
    = G_N(T_v f, T_v f) - 2 G_N(T_v f, T_{w_n} f) + G_N(T_{w_n} f, T_{w_n} f)
    = 2 G_N(f, f) - 2 G_N(f, T_{v-w_n} f)

(using Green's function translation invariance G(T_u g, T_u h) = G(g, h))

As w_n -> v, we have v - w_n -> 0, so T_{v-w_n} f -> f in the test function
topology, and G_N(f, T_{v-w_n} f) -> G_N(f, f) by continuity. Combined with
propagator convergence G_N -> G, this gives G_N(h_n, h_n) -> 0.

### Step 5: Assembly

Combining Steps 2-4:
  |Z_{phi(n)+1}[T_v f] - Z_{phi(n)+1}[f]| -> 0

By weak convergence:
  Z_{phi(n)+1}[T_v f] -> Z[T_v f]
  Z_{phi(n)+1}[f] -> Z[f]

By uniqueness of limits: Z[T_v f] = Z[f].

## Why the Second Moment Suffices

The generating functional Z[f] = E[exp(i omega(f))] has the remarkable property
that its continuity is controlled by the **second** moment alone:

  |Z[f] - Z[g]| <= E[|exp(i omega(f)) - exp(i omega(g))|]
                 <= E[|omega(f - g)|]           (|exp(ix)-exp(iy)| <= |x-y|)
                 <= sqrt(E[(omega(f-g))^2])      (Cauchy-Schwarz, prob. measure)

This is because exp(i*) is bounded by 1 and Lipschitz with constant 1.

Higher-point functions (Schwinger functions) S_n(f_1,...,f_n) do NOT need
separate translation invariance proofs: once Z is translation-invariant,
it determines the measure mu_P uniquely, and all Schwinger functions inherit
the symmetry automatically.

The **exponential moment bound** E_P[exp(|omega(f)|)] <= K * exp(G(f,f))
(already proved) gives even stronger control, bounding ALL moments simultaneously.

## Axioms Used

1. `torusInteractingMeasure_gf_latticeTranslation_invariant` - lattice GF invariance
2. `torus_interacting_second_moment_continuous` - interacting-to-Gaussian bridge
3. `gaussian_exp_abs_moment` - Gaussian exponential moments (for OS0/OS1)
4. Green's function translation invariance (proved in gaussian-field)
5. Propagator convergence G_N -> G (proved)

## References

- Glimm-Jaffe, *Quantum Physics*, Section 8.1 (lattice translation invariance)
- Simon, *The P(phi)_2 Euclidean QFT*, Chapter V, Section 1
- Nelson (1966), Section 5 (translation invariance of the continuum limit)
