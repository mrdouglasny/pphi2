/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L² bound on the rough-field error

Step 1 of the discharge of `polynomial_chaos_exp_moment_bridge`. Bounds
the L² norm (variance) of the rough-field error of a Wick-polynomial
interaction on the canonical joint Gaussian measure.

## Main result

`rough_error_variance` — for any `InteractionPolynomial P`,
`∫ E_R² ∂μ_joint ≤ K · T · (1 + |log T|)^{P.n − 1}`
with `K` uniform in `(a, N)` at fixed `(L, mass, P)`.

Phase 2 (separate file) will feed this into `polynomial_chaos_concentration`
(Janson's Theorem 5.10, available in `gaussian-hilbert`) to obtain the L^p
and stretched-exponential tail bounds needed by `LatticeRoughErrorSetup`.

## Plan

See `docs/rough-error-variance-plan.md` for the full step-by-step plan and
review history. Five-step structure (S1–S5: pointwise binomial decomposition,
reindexing by smooth/rough degree pair, cross-term orthogonality on the
joint measure, per-term L² bound, final assembly).

## Upstream prerequisites (sorry'd, Phase 2 textbook discharge)

Two `(a, N)`-uniform Glimm–Jaffe Ch. 8 (Thm 8.5.2) Fourier estimates:
- `canonicalSmoothCovariance_le_log` — smooth covariance L^∞ uniform
- `canonicalRoughCovariance_pow_sum_le` — rough covariance L^m sum uniform

Quarantined to `CovarianceSplit.lean` once Codex hits the exact API needed.

## References

- Glimm–Jaffe, *Quantum Physics*, Ch. 8 (dynamical cutoff, Theorem 8.5.2)
- Simon, *The P(φ)₂ Euclidean Quantum Field Theory*, Ch. V (Nelson estimate)
- Janson, *Gaussian Hilbert Spaces*, Theorem 5.10 (polynomial-chaos
  concentration)
-/

import Pphi2.NelsonEstimate.FieldDecomposition
import Pphi2.WickOrdering.WickPolynomial

noncomputable section

open MeasureTheory GaussianField
open scoped BigOperators

namespace Pphi2

variable (d N : ℕ) [NeZero N] (a mass : ℝ)

/-! ## Definitions

Three random variables on the canonical joint Gaussian measure
`canonicalJointMeasure d N = Measure.prod (Π gaussianReal) (Π gaussianReal)`:

* `canonicalSmoothInteraction P T η` — Wick polynomial of `P` evaluated at
  the smooth field, with smooth Wick subtraction `c_S = smoothWickConstant`,
  weighted by lattice volume `a^d` and summed over sites.
* `canonicalFullInteractionJoint P T η` — Wick polynomial of `P` evaluated
  at the full field `φ_S + φ_R`, with full Wick subtraction `c = wickConstant`.
* `canonicalRoughError P T η` — the difference. By the Wick binomial
  identity (`wickMonomial_add_binomial`), this is a sum of cross-terms
  each containing at least one rough-field factor `:φ_R^m:` with `m ≥ 1`.

Names are deliberately distinct from `latticeSmoothInteraction` /
`latticeRoughError` in `LatticeSetup.lean`, which are deterministic
versions on `Configuration` for the dynamical-cutoff layer-cake.
-/

/-- Wick-polynomial interaction evaluated at the smooth field, weighted
by lattice volume and summed over sites. Lives on the canonical joint
Gaussian measure. -/
def canonicalSmoothInteraction (T : ℝ) (P : InteractionPolynomial)
    (η : CanonicalJoint d N) : ℝ :=
  a ^ d * ∑ x : FinLatticeSites d N,
    wickPolynomial P (smoothWickConstant d N a mass T)
      (canonicalSmoothFieldFunction d N a mass T η x)

/-- Wick-polynomial interaction evaluated at the full field `φ_S + φ_R`,
weighted by lattice volume and summed over sites. Lives on the canonical
joint Gaussian measure. -/
def canonicalFullInteractionJoint (T : ℝ) (P : InteractionPolynomial)
    (η : CanonicalJoint d N) : ℝ :=
  a ^ d * ∑ x : FinLatticeSites d N,
    wickPolynomial P (wickConstant d N a mass)
      (canonicalSumFieldFunction d N a mass T η x)

/-- The rough-field error: full Wick interaction minus smooth Wick
interaction. By `wickMonomial_add_binomial` + cancellation of the all-smooth
term, this expands to a sum of cross-terms each containing at least one
factor `:φ_R^m:` with `m ≥ 1`. -/
def canonicalRoughError (T : ℝ) (P : InteractionPolynomial)
    (η : CanonicalJoint d N) : ℝ :=
  canonicalFullInteractionJoint d N a mass T P η -
    canonicalSmoothInteraction d N a mass T P η

/-! ## S1–S2 (skeleton): pointwise binomial decomposition + reindex

The pointwise decomposition expresses the rough error as a sum over
`(j, m)` pairs with `j + m ≤ P.n` and `m ≥ 1`, of
`A(j,m) · :φ_S^j(x):_{c_S} · :φ_R^m(x):_{c_R}` weighted by `a^d` and
summed over sites. The proof uses `wickMonomial_add_binomial` per
monomial of `P`, then cancels the `m = 0` (all-smooth) term.

Stub for now; concrete content to follow in subsequent commits.
-/

/-- The rough error equals the per-site difference of full minus smooth
Wick polynomials. Trivial unfolding; useful as the starting point for
the binomial decomposition (S1). -/
lemma canonicalRoughError_eq_sum_diff (T : ℝ) (P : InteractionPolynomial)
    (η : CanonicalJoint d N) :
    canonicalRoughError d N a mass T P η =
      a ^ d * ∑ x : FinLatticeSites d N,
        (wickPolynomial P (wickConstant d N a mass)
            (canonicalSumFieldFunction d N a mass T η x) -
          wickPolynomial P (smoothWickConstant d N a mass T)
            (canonicalSmoothFieldFunction d N a mass T η x)) := by
  unfold canonicalRoughError canonicalFullInteractionJoint canonicalSmoothInteraction
  rw [← mul_sub, ← Finset.sum_sub_distrib]

/-! ## Main theorem (statement, proof TBD)

`rough_error_variance` quantifies `K` outside the lattice binders so it
cannot depend on `(a, N)` and break continuum-limit uniformity. The
constraint `(N : ℝ) * a = L` pins the macroscopic period. The polylog
exponent `P.n − 1` is the maximum power of `‖C_S‖_∞ ≤ 1 + |log T|` that
appears in any cross-term (since `m ≥ 1` forces `j ≤ P.n − 1`).
-/

/-- **L² bound on the rough-field error** of a Wick-polynomial interaction.

For any `InteractionPolynomial P` and macroscopic period `L > 0`, there
exists a constant `K(P, mass, L) > 0` such that for every lattice
discretization `(N, a)` with `(N : ℝ) * a = L`,

  `∫ η, (canonicalRoughError d N a mass T P η)² ∂(canonicalJointMeasure d N)
    ≤ K · T · (1 + |log T|)^{P.n − 1}`.

The bound is uniform in `(a, N)` at fixed `(L, mass, P)`. The polylog
factor comes from the smooth covariance `‖C_S‖_∞ ≤ A + B · |log T|`;
the linear `T` factor comes from the rough covariance L^m summability.

This is **Step 1** of the discharge of `polynomial_chaos_exp_moment_bridge`
(`PolynomialChaosBridge.lean:116`). Phase 2 feeds this into
`polynomial_chaos_concentration` (Janson 5.10) for L^p and tail bounds.

See `docs/rough-error-variance-plan.md` for the full proof plan. -/
theorem rough_error_variance
    {d : ℕ} (P : InteractionPolynomial)
    (L mass : ℝ) (_hL : 0 < L) (_hmass : 0 < mass)
    (T : ℝ) (_hT : 0 < T) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a)
        (_h_vol : (N : ℝ) * a = L),
        ∫ η, (canonicalRoughError d N a mass T P η) ^ 2
          ∂(canonicalJointMeasure d N) ≤
        K * T * (1 + |Real.log T|) ^ (P.n - 1) := by
  sorry

end Pphi2

end
