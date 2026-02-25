# Hypercontractivity Proof Plans

*Updated 2026-02-24*

## Overview

Plans for proving the Option A axioms in `Pphi2/ContinuumLimit/Hypercontractivity.lean`.
Option A uses 3 axioms (Hölder + exponential moments approach).

## History: Holley-Stroock Approach Was Wrong

Gemini deep think (2026-02-24) flagged that `wick_action_bounded_oscillation`
(bounded oscillation of V_a) is mathematically incorrect for P(φ)₂. The
Wick-ordered action V_a grows like φ⁴, so osc(V_a) = ∞. Holley-Stroock
requires bounded perturbations.

Replaced with the standard Hölder + exponential moments approach.

## Subtlety: exponential_moment_bound is DEEP

Gemini deep think (2026-02-24, second consultation) clarified that the simple
argument "V_a ≥ -B implies exp(-V_a) ≤ exp(B)" does NOT give a uniform-in-a
bound, because:

1. The Wick constant c_a ~ (1/2π)log(1/a) diverges as a → 0
2. The lower bound B on :P(φ(x)):_a depends on c_a, hence on a
3. The number of lattice sites |Λ| ~ 1/a² grows as a → 0
4. So the total lower bound on V_a = a²Σ_x :P(φ(x)):_a is NOT uniform

The uniform exponential moment bound

  sup_a ∫ exp(-s·V_a) dμ_{GFF} ≤ K_s < ∞

is a **deep stability estimate** from the Glimm-Jaffe program, proved
via cluster expansions. It is one of the main technical achievements of
constructive QFT.

Reference: Glimm-Jaffe (1987), Theorem 8.6.1; Simon (1974), §V.

## Option A Axiom Plans

### Axiom 1: `gaussian_hypercontractivity_continuum` — Medium

**Statement:** Gaussian hypercontractivity for the pushforward (ι_a)_*μ_{GFF}.

**Proof strategy:**
- ω(f) under (ι_a)_*μ_{GFF} is Gaussian with variance ⟨f, G_a f⟩
- Apply `gaussian_hypercontractive` from gaussian-field (already proved)
- Pushforward preserves the inequality

**Infrastructure needed:**
- `pairing_is_gaussian` from gaussian-field
- `Measure.map` integral formula

**Difficulty:** Medium (type plumbing, not hard math).

### Axiom 2: `exponential_moment_bound` — Hard (deep C-QFT result)

**Statement:** ∫ exp(-V_a)² dμ_{GFF} ≤ K uniformly in a.

**This is a fundamental axiom, not something we can easily prove.** It
encodes the stability of the P(φ)₂ interaction — the fact that the
Boltzmann weight exp(-V_a) has uniformly controlled moments despite
the Wick constant diverging.

**Proof in the literature:**
- Nelson's estimate + cluster expansions (Glimm-Jaffe)
- Essentially: decompose V_a into local contributions, use
  independence structure of the GFF, control via Wick ordering
  + hypercontractivity of Gaussian moments
- Super-renormalizability (d=2) is crucial — ensures only finitely
  many divergent counterterms

**For the formalization:** Keep as axiom. The axiom says: the P(φ)₂
construction is stable. This is the analytic heart of the theory.

**Difficulty:** Hard (literature result, not provable from current Lean infra).

### Axiom 3: `hoelder_transfer` — Medium

**Statement:** Transfer from Gaussian to interacting measure via Hölder.

**Proof strategy (Hölder with exponents r, s):**
1. ∫|F|^p dμ_a = (1/Z_a) ∫|F|^p · e^{-V_a} dμ_{GFF}
2. Hölder: ≤ (1/Z_a) · (∫|F|^{pr} dμ_{GFF})^{1/r} · (∫e^{-sV_a} dμ_{GFF})^{1/s}
3. Apply Gaussian hypercontractivity to first factor
4. Apply exponential_moment_bound to second factor
5. Z_a ≥ Z_min > 0 from partitionFunction_pos

**Subtlety (from Gemini):** The Hölder approach gives a bound involving
‖F‖_{L^{pr}(μ_GFF)}, not ‖F‖_{L²(μ_a)}. The current axiom statement
has the RHS in terms of μ_a. This is the correct final form (it's the
hypercontractive inequality for the interacting theory), but deriving it
from the Hölder bound requires additional work:
- Either state the axiom with RHS in terms of μ_{GFF} (simpler to prove)
- Or include the conversion back to μ_a norms (requires another
  application of the density bound)

**Note:** The current axiom statement may need revision to match what
the Hölder argument actually proves. The standard result is:

  ‖T_t F‖_{Lp(μ_a)} ≤ ‖F‖_{Lq(μ_a)}

where T_t = exp(-tH_a) is the interacting semigroup and
p = 1 + e^{2ρt}(q-1). For Wick monomials (eigenfunctions with eigenvalue n),
this gives the (p-1)^{n/2} bound.

**Difficulty:** Medium (measure theory plumbing).

## Summary

| Axiom | Difficulty | Status |
|-------|-----------|--------|
| `gaussian_hypercontractivity_continuum` | Medium | Provable from gaussian-field |
| `exponential_moment_bound` | Hard | Deep C-QFT stability estimate — keep as axiom |
| `hoelder_transfer` | Medium | Provable from axioms 1+2 via Hölder |

The key mathematical content is in Axiom 2 (exponential moment bound).
Axioms 1 and 3 are standard measure theory / functional analysis.

## Option B Axioms (Gross-Rothaus-Simon) — Not Required

5 additional axioms providing the full OU semigroup framework.
See `Hypercontractivity.lean` for descriptions.

## References

- Simon (1974), *The P(φ)₂ Euclidean QFT*, §V
- Glimm-Jaffe (1987), *Quantum Physics*, Theorem 8.6.1, §19.1, §19.4
- Gross (1975), "Logarithmic Sobolev inequalities"
- Nelson (1973), "The free Markoff field"
- Holley-Stroock (1987) — does NOT apply (V_a unbounded)
