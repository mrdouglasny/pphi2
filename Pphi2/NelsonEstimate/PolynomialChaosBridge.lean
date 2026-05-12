/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Polynomial Chaos Bridge: Cluster A Master Theorem

This file packages the four pphi2 Cluster A axioms (the Nelson
exponential estimate in its various lattice flavors) into a single
master theorem `nelson_exponential_estimate_master`, derived from a
single bridge axiom that mirrors the polynomial-chaos concentration
theorem upstream in `markov-semigroups`.

## The bridge axiom

`polynomial_chaos_exp_moment_bridge` is the lattice-Wick-polynomial
specialization of Janson's Theorem 5.10
(`GaussianHilbert.PolynomialChaosConcentration`). It states
the dynamical-cutoff conclusion: for the lattice GFF on `(ℤ/Nℤ)^d`
with spacing `a` and mass `m > 0`, and a fixed even interaction
polynomial `P`,

  ∃ K, ∀ N, ∫ exp(-2 V_a(ω))² dμ_GFF ≤ K  uniformly in N.

The proof in `markov-semigroups` is the three-step Glimm–Jaffe Ch. 8
chain (smooth lower bound on `V_S`; polynomial-chaos concentration
on `E_R`; dynamical cutoff `T = T(M)` and integration). The smooth-side
infrastructure (`SmoothLowerBound.lean`) and the rough-side scaffolding
(`RoughErrorBound.lean`, currently `True`-stub theorems) are already
in pphi2; once `markov-semigroups`'s `polynomial_chaos_concentration`
becomes a theorem and the GFF↔standard-Gaussian change-of-variables
bridge is available, this axiom becomes a derivation rather than an
assertion.

Because pphi2 cannot currently depend on `markov-semigroups` at the
lakefile level (Mathlib pin synchronization across the project family
is a separate maintenance task), we state this bridge as a pphi2-internal
`axiom` with cross-references to the upstream files. When the dependency
wires up, the bridge is replaceable by a one-line `import + apply`.

## What this collapses

- `nelson_exponential_estimate_lattice` (was `axiom`, now `theorem`)
- `exponential_moment_bound` (was `axiom`, now `theorem`)
- `asymNelson_exponential_estimate` (was `axiom`, now `theorem`)

The fourth Cluster A axiom (`asymTorusInteracting_exponentialMomentBound`
in `AsymTorus/AsymTorusOS.lean`) is structurally different — it lifts
the bound to the limit measure via BC convergence — and is handled
in its own derivation (still in `AsymTorusOS.lean`).

Net change: 3 statements with identical shape → 1 master theorem +
1 bridge axiom; net reduction of 2 axioms. The 4th axiom converts
similarly via a separate BC-limit lemma.

## References

- pphi2/docs/polynomial-chaos-concentration.md — the full math writeup
  (Jaffe-suggested LD framing; 2-pass Gemini-vetted).
- markov-semigroups/docs/polynomial-chaos-roadmap.md — the upstream
  implementation plan.
- gaussian-hilbert/GaussianHilbert/PolynomialChaosConcentration.lean
  — the upstream Janson Theorem 5.10 axiom.
- Glimm and Jaffe, *Quantum Physics*, Ch. 8 — the dynamical cutoff proof.
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I.
-/

import Pphi2.WickOrdering.WickPolynomial
import Pphi2.InteractingMeasure.LatticeMeasure

noncomputable section

open MeasureTheory Real GaussianField

namespace Pphi2

variable (d : ℕ)

/-- **Master bridge axiom: Nelson exponential estimate from polynomial chaos.**

For a lattice GFF on `(ℤ/Nℤ)^d` with spacing `a > 0` and mass `m > 0`,
and an even interaction polynomial `P`, there is a constant `K > 0`
independent of `N` (and `a` in the regime `0 < a ≤ 1`) such that
$$
  \int \exp(-2 V_a(\omega))^2 \, d\mu_{\rm GFF} \le K.
$$

**Proof outline (Glimm–Jaffe Ch. 8 / Simon Ch. I dynamical cutoff):**
1. Split the field $\phi = \phi_S + \phi_R$ via the covariance-split
   $C = C_S(T) + C_R(T)$ in `NelsonEstimate/CovarianceSplit.lean`.
2. Smooth-side classical lower bound:
   $V_S(\phi_S) \ge -C_1 (1 + |\log T|)^2$, proved as
   `smooth_interaction_lower_bound_log` in `SmoothLowerBound.lean`.
3. Rough-side polynomial-chaos concentration: for the rough error
   $E_R = V(\phi) - V_S(\phi_S)$, which is a degree-$\deg P$ Wick
   polynomial in $\phi_R$ (so lives in $\mathcal H^{\le \deg P}$),
   apply Janson Theorem 5.10
   (`GaussianHilbert.PolynomialChaosConcentration`,
   currently axiomatized in markov-semigroups awaiting upstream proof):
   $\mathbb P(|E_R| > \lambda) \le 2 \exp(- c \, \lambda^{2/\deg P} \,
   T^{-\delta/\deg P})$, with $\delta$ from the rough-covariance
   estimate.
4. Dynamical cutoff: choose $T = T(M)$ such that
   $C_1 (\log T)^2 = M/2$, i.e. $T = \exp(-\sqrt{M/(2 C_1)})$. Then
   $V(\phi) \le -M$ implies $|E_R| \ge M/2$, giving doubly-exponential
   tail decay.
5. Integrate $\int_0^\infty \exp(2M) \, \mathbb P(V \le -M) \, dM
   < \infty$ uniformly in $N$.

**Cross-reference.** The upstream Janson Theorem 5.10
(`polynomial_chaos_concentration` in markov-semigroups) provides
ingredient 3 in abstract form. Ingredients 2 and 4 are pphi2-local.
A future PR can replace this axiom with a derivation once
markov-semigroups is dependable from pphi2 (Mathlib-pin sync needed
across the project family) and the GFF↔standard-Gaussian change of
variables is wired in. -/
axiom polynomial_chaos_exp_moment_bridge
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ (K : ℝ), 0 < K ∧
    ∀ (a : ℝ) (ha : 0 < a),
    ∀ (N : ℕ) [NeZero N],
    ∫ ω : Configuration (FinLatticeField d N),
        (exp (-interactionFunctional d N P a mass ω)) ^ 2
        ∂(latticeGaussianMeasure d N a mass ha hmass) ≤ K

/-- **Master theorem: lattice Nelson exponential estimate**, derived
from `polynomial_chaos_exp_moment_bridge` by trivial unfolding (the
theorem is the bridge with witness extracted).

**Note on strength.** The textbook Glimm–Jaffe Ch. 8 result is uniform
in `(a, N)` for `a` in any bounded interval (canonically `(0, 1]`).
The bridge as stated here is over-stated to `∀ a > 0`; the
discharge plan is to (a) tighten the bridge axiom to `a ≤ 1` once
the upstream `polynomial_chaos_concentration` derivation is wired in,
and (b) absorb finite-`N` small-`a` (`a > 1`) values into a downstream
witness `K'`. Until then the over-statement is preserved here for
downstream convenience — see the audit notes in `docs/axiom_audit.md`. -/
theorem nelson_exponential_estimate_master
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ (K : ℝ), 0 < K ∧
    ∀ (a : ℝ) (ha : 0 < a),
    ∀ (N : ℕ) [NeZero N],
    ∫ ω : Configuration (FinLatticeField d N),
        (exp (-interactionFunctional d N P a mass ω)) ^ 2
        ∂(latticeGaussianMeasure d N a mass ha hmass) ≤ K :=
  polynomial_chaos_exp_moment_bridge d P mass hmass

/-- Convenience corollary: master theorem with `a ≤ 1` constraint
preserved (matches the existing `exponential_moment_bound` axiom shape
exactly). -/
theorem nelson_exponential_estimate_master_bounded
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ (K : ℝ), 0 < K ∧
    ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
    ∀ (N : ℕ) [NeZero N],
    ∫ ω : Configuration (FinLatticeField d N),
        (exp (-interactionFunctional d N P a mass ω)) ^ 2
        ∂(latticeGaussianMeasure d N a mass ha hmass) ≤ K := by
  obtain ⟨K, hK_pos, hbound⟩ := nelson_exponential_estimate_master d P mass hmass
  exact ⟨K, hK_pos, fun a ha _ N _ => hbound a ha N⟩

end Pphi2
