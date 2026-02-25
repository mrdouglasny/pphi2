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

### ~~Theorem 1: `gaussian_hypercontractivity_continuum`~~ — PROVED

**Statement:** Gaussian hypercontractivity for the pushforward (ι_a)_*μ_{GFF}.

**Proof:** Proved by reducing to `gaussian_hypercontractive` from gaussian-field.
Key steps: `integral_map` to pull back from S'(ℝ^d) to lattice, then
`latticeEmbedLift_eval_eq` to rewrite `(ι_a ω)(f) = ω(g_f)` where g_f is the
embedded test function, reducing to an instance of the abstract bound.

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

### Axiom 3: `interacting_moment_bound` — Medium

**Statement:** Bounds interacting L^{pn} moments in terms of FREE Gaussian
L^{2n} moments.

**Key mathematical point:** The RHS uses the FREE Gaussian measure μ_{GFF},
NOT the interacting measure μ_a. The earlier `hoelder_transfer` axiom had
both sides in terms of μ_a, which is UNPROVABLE because converting the
RHS back from μ_{GFF} to μ_a requires bounding ∫ e^{+V_a} dμ_{GFF}, and
since V_a ~ φ⁴ grows faster than the Gaussian suppression e^{-φ²}, this
integral diverges to infinity.

**Proof strategy (Cauchy-Schwarz with r=s=2):**
1. ∫|F|^{pn} dμ_a = (1/Z_a) ∫|F|^{pn} · e^{-V_a} dμ_{GFF}
2. Cauchy-Schwarz: ≤ (1/Z_a) · (∫|F|^{2pn} dμ_{GFF})^{1/2} · (∫e^{-2V_a} dμ_{GFF})^{1/2}
3. Apply `exponential_moment_bound` to bound second factor by K^{1/2}
4. Apply `gaussian_hypercontractivity_continuum` with exponent 2p to first factor:
   (∫|F|^{2pn} dμ_{GFF})^{1/2} ≤ (2p-1)^{pn/2} · (∫|F|^{2n} dμ_{GFF})^{p/2}
5. Combine: ∫|F|^{pn} dμ_a ≤ (K^{1/2}/Z_a) · (2p-1)^{pn/2} · (∫|F|^{2n} dμ_{GFF})^{p/2}

**Why this suffices for tightness:** Setting p=2, n=1 gives:
  ∫|ω f|² dμ_a ≤ C · 3 · ∫|ω f|² dμ_{GFF} = C · 3 · ⟨f, G_a f⟩
which is trivially bounded uniformly in a since G_a → G in operator norm.

**Difficulty:** Medium (Cauchy-Schwarz for Bochner integrals + measurability).

## Summary

| Axiom/Theorem | Difficulty | Status |
|-------|-----------|--------|
| ~~`gaussian_hypercontractivity_continuum`~~ | Medium | **PROVED** from gaussian-field via pushforward |
| `exponential_moment_bound` | Hard | Deep C-QFT stability estimate — keep as axiom |
| `interacting_moment_bound` | Medium | Provable from theorem 1 + axiom 2 via Cauchy-Schwarz |

The key mathematical content is in Axiom 2 (exponential moment bound).
Theorem 1 is proved and Axiom 3 is standard measure theory (Cauchy-Schwarz).

## Option B Axioms (Gross-Rothaus-Simon) — Not Required

5 additional axioms providing the full OU semigroup framework.
See `Hypercontractivity.lean` for descriptions.

## References

- Simon (1974), *The P(φ)₂ Euclidean QFT*, §V
- Glimm-Jaffe (1987), *Quantum Physics*, Theorem 8.6.1, §19.1, §19.4
- Gross (1975), "Logarithmic Sobolev inequalities"
- Nelson (1973), "The free Markoff field"
- Holley-Stroock (1987) — does NOT apply (V_a unbounded)
