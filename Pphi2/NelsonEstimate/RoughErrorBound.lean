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

/-! ## S1: pointwise binomial decomposition

Expand each per-site difference of Wick polynomials via the binomial
identity `wickPolynomial_add_sub_self` (which itself comes from
`wickMonomial_add_binomial` plus cancellation of the all-smooth term).
After substituting the covariance split `c = c_S + c_R` (via
`wickConstant_split`) and the field split `φ = φ_S + φ_R` (via
`canonicalSumFieldFunction_eq_smooth_plus_rough`), the rough error
becomes a finite sum of cross-terms each containing at least one
factor `:φ_R^{k - j}:_{c_R}` with `k - j ≥ 1`.

S2 (reindexing the (k, j) sum by (j, m := k − j) with `m ≥ 1`) is
done in subsequent lemmas as needed for S3/S4. -/

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

/-- **S1: pointwise binomial decomposition.** The rough error expands
into cross-terms `:φ_S^k:_{c_S} · :φ_R^{n − k}:_{c_R}` (one per leading
binomial index `k < P.n`) plus per-coefficient cross-terms
`:φ_S^k:_{c_S} · :φ_R^{m − k}:_{c_R}` (one per `(m, k)` with `m < P.n`,
`k < m`), each weighted by `a^d` and summed over sites. The constraint
`k < · ` (strict) comes from cancellation of the all-smooth `k = ·` term
against `canonicalSmoothInteraction`.

This is the algebraic content of S1 in
`docs/rough-error-variance-plan.md`. The proof uses
`wickPolynomial_add_sub_self` after substituting the covariance and
field splits. -/
lemma canonicalRoughError_pointwise_decomposition
    (T : ℝ) (P : InteractionPolynomial) (η : CanonicalJoint d N) :
    canonicalRoughError d N a mass T P η =
    a ^ d * ∑ x : FinLatticeSites d N,
      ((1 / P.n : ℝ) * ∑ k ∈ Finset.range P.n,
          (P.n.choose k : ℝ) *
            wickMonomial k (smoothWickConstant d N a mass T)
              (canonicalSmoothFieldFunction d N a mass T η x) *
            wickMonomial (P.n - k) (roughWickConstant d N a mass T)
              (canonicalRoughFieldFunction d N a mass T η x)
      + ∑ m : Fin P.n, P.coeff m * ∑ k ∈ Finset.range (m : ℕ),
          ((m : ℕ).choose k : ℝ) *
            wickMonomial k (smoothWickConstant d N a mass T)
              (canonicalSmoothFieldFunction d N a mass T η x) *
            wickMonomial ((m : ℕ) - k) (roughWickConstant d N a mass T)
              (canonicalRoughFieldFunction d N a mass T η x)) := by
  rw [canonicalRoughError_eq_sum_diff]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [wickConstant_split d N a mass T,
      canonicalSumFieldFunction_eq_smooth_plus_rough d N a mass T η x]
  exact wickPolynomial_add_sub_self P
    (smoothWickConstant d N a mass T)
    (roughWickConstant d N a mass T)
    (canonicalSmoothFieldFunction d N a mass T η x)
    (canonicalRoughFieldFunction d N a mass T η x)

/-! ## S2: reindex by (smooth-degree, rough-degree)

Define the per-(k, j) cross-term `M_{k,j}(η) = a^d · Σ_x :φ_S^j(x):_{c_S}
· :φ_R^{k-j}(x):_{c_R}`. The rough error is then a finite sum
`Σ_{(k, j)} A(k, j) · M_{k, j}(η)` where `A(k, j) = (Polynomial coeff at
degree k) · C(k, j)`. The constraint `j < k` (so `k - j ≥ 1`, at least
one rough factor) is inherited from S1.

This is the form S3 (Wick cross-term orthogonality) and S4 (per-term L²
bound) consume directly. -/

/-- Per-`(k, j)` cross-term of the rough error: `a^d` times the
position-sum of `:φ_S^j(x):_{c_S} · :φ_R^{k-j}(x):_{c_R}`. The L² norm
of the rough error decomposes (via Wick orthogonality) as a sum of L²
norms of these cross-terms. -/
def canonicalCrossTerm (T : ℝ) (η : CanonicalJoint d N) (k j : ℕ) : ℝ :=
  a ^ d * ∑ x : FinLatticeSites d N,
    wickMonomial j (smoothWickConstant d N a mass T)
      (canonicalSmoothFieldFunction d N a mass T η x) *
    wickMonomial (k - j) (roughWickConstant d N a mass T)
      (canonicalRoughFieldFunction d N a mass T η x)

/-- **S2: reindex pointwise decomposition into a sum of named cross-terms.**
The rough error equals a `(P.coeff)`-weighted sum of `canonicalCrossTerm`
values, with the leading `(1 / P.n)` term handled separately. The sum
range `j ∈ Finset.range k` ensures `k - j ≥ 1` (at least one rough
factor per term). -/
lemma canonicalRoughError_eq_sum_over_cross_terms
    (T : ℝ) (P : InteractionPolynomial) (η : CanonicalJoint d N) :
    canonicalRoughError d N a mass T P η =
    (1 / P.n : ℝ) * ∑ j ∈ Finset.range P.n,
        (P.n.choose j : ℝ) * canonicalCrossTerm d N a mass T η P.n j
    + ∑ m : Fin P.n, P.coeff m *
        ∑ j ∈ Finset.range (m : ℕ),
          ((m : ℕ).choose j : ℝ) *
            canonicalCrossTerm d N a mass T η (m : ℕ) j := by
  rw [canonicalRoughError_pointwise_decomposition]
  -- Strategy:
  -- (1) split the per-x sum over the (lead + terms) structure;
  -- (2) for each piece, push a^d and outer scalars inside the sum,
  --     swap Σ_x with the binomial-index Σ_j (or Σ_m, Σ_j), then pull
  --     coefficients back out and recognise canonicalCrossTerm.
  rw [Finset.sum_add_distrib, mul_add]
  unfold canonicalCrossTerm
  refine congr_arg₂ (· + ·) ?_ ?_
  · -- Leading (1/n) term:
    -- a^d * Σ_x (1/n * Σ_j C(n,j) * sm_j * ru_{n-j})
    --   = (1/n) * Σ_j C(n,j) * (a^d * Σ_x sm_j * ru_{n-j})
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [mul_assoc, ← Finset.mul_sum]
    ring
  · -- Per-coefficient terms:
    -- a^d * Σ_x Σ_m c_m * Σ_j C(m,j) * sm_j * ru_{m-j}
    --   = Σ_m c_m * Σ_j C(m,j) * (a^d * Σ_x sm_j * ru_{m-j})
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [mul_assoc, ← Finset.mul_sum]
    ring

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
