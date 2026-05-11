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

/-! ## Generic L² Pythagoras (two functions)

Reusable: when `∫ L · R = 0`, `∫ (L + R)² = ∫ L² + ∫ R²`. Pure
integration linearity + the orthogonality input. Used to combine the
leading and per-coefficient pieces of `canonicalRoughError`. -/

/-- L² Pythagoras for two real-valued functions whose cross integral
vanishes. Pure integration linearity. -/
lemma integral_sq_add_of_inner_eq_zero
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (L R : α → ℝ)
    (h_orth : ∫ x, L x * R x ∂μ = 0)
    (h_int_LL : Integrable (fun x => L x ^ 2) μ)
    (h_int_RR : Integrable (fun x => R x ^ 2) μ)
    (h_int_LR : Integrable (fun x => L x * R x) μ) :
    ∫ x, (L x + R x) ^ 2 ∂μ = ∫ x, L x ^ 2 ∂μ + ∫ x, R x ^ 2 ∂μ := by
  -- (L + R)² = L² + 2(LR) + R² pointwise
  have h_expand : ∀ x, (L x + R x) ^ 2 =
      L x ^ 2 + 2 * (L x * R x) + R x ^ 2 := by intros; ring
  have h_int_2LR : Integrable (fun x => 2 * (L x * R x)) μ := h_int_LR.const_mul 2
  calc ∫ x, (L x + R x) ^ 2 ∂μ
      = ∫ x, L x ^ 2 + 2 * (L x * R x) + R x ^ 2 ∂μ := by
        simp_rw [h_expand]
    _ = (∫ x, L x ^ 2 + 2 * (L x * R x) ∂μ) + ∫ x, R x ^ 2 ∂μ :=
        MeasureTheory.integral_add (h_int_LL.add h_int_2LR) h_int_RR
    _ = ∫ x, L x ^ 2 ∂μ + ∫ x, 2 * (L x * R x) ∂μ + ∫ x, R x ^ 2 ∂μ := by
        rw [MeasureTheory.integral_add h_int_LL h_int_2LR]
    _ = ∫ x, L x ^ 2 ∂μ + 2 * ∫ x, L x * R x ∂μ + ∫ x, R x ^ 2 ∂μ := by
        rw [MeasureTheory.integral_const_mul]
    _ = ∫ x, L x ^ 2 ∂μ + 2 * 0 + ∫ x, R x ^ 2 ∂μ := by rw [h_orth]
    _ = ∫ x, L x ^ 2 ∂μ + ∫ x, R x ^ 2 ∂μ := by ring

/-! ## Generic L²-orthogonality reduction

Reusable lemma not specific to the rough-error setting: for a finite-indexed
family `f i` of real-valued functions that are pairwise L²-orthogonal under
a measure `μ`, the integral of the squared real-coefficient sum reduces to
a single sum of squared coefficients times squared L² norms (no off-diagonal
contribution).

Given:
- `s : Finset ι` and `f : ι → α → ℝ` with `a : ι → ℝ` coefficients,
- pairwise orthogonality `∫ f i · f j ∂μ = 0` for `i ≠ j` in `s`,
- pairwise integrability of products `f i · f j`,

then `∫ (∑ i, a i · f i)² ∂μ = ∑ i, (a i)² · ∫ (f i)² ∂μ`. -/
lemma integral_sq_real_sum_of_pairwise_orthogonal
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) (f : ι → α → ℝ) (a : ι → ℝ)
    (h_orth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∫ x, f i x * f j x ∂μ = 0)
    (h_int : ∀ i ∈ s, ∀ j ∈ s, Integrable (fun x => f i x * f j x) μ) :
    ∫ x, (∑ i ∈ s, a i * f i x) ^ 2 ∂μ =
    ∑ i ∈ s, (a i) ^ 2 * ∫ x, (f i x) ^ 2 ∂μ := by
  classical
  -- Step 1: expand the square pointwise as a double sum
  have h_expand : (fun x => (∑ i ∈ s, a i * f i x) ^ 2) =
      (fun x => ∑ i ∈ s, ∑ j ∈ s, (a i * a j) * (f i x * f j x)) := by
    funext x
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h_expand]
  -- Step 2: integration linearity (outer sum)
  have h_int_inner : ∀ i ∈ s, Integrable
      (fun x => ∑ j ∈ s, (a i * a j) * (f i x * f j x)) μ := by
    intros i hi
    apply MeasureTheory.integrable_finset_sum
    intros j hj
    exact (h_int i hi j hj).const_mul (a i * a j)
  rw [MeasureTheory.integral_finset_sum s h_int_inner]
  refine Finset.sum_congr rfl fun i hi => ?_
  -- Step 3: integration linearity (inner sum) + pull constants out
  rw [MeasureTheory.integral_finset_sum s
        (fun j hj => (h_int i hi j hj).const_mul (a i * a j))]
  have h_const : ∀ j ∈ s,
      ∫ x, (a i * a j) * (f i x * f j x) ∂μ =
      (a i * a j) * ∫ x, f i x * f j x ∂μ := by
    intros j _
    exact MeasureTheory.integral_const_mul _ _
  rw [Finset.sum_congr rfl h_const]
  -- Step 4: split diagonal vs off-diagonal; off-diagonal vanishes by orthogonality
  rw [show ∑ j ∈ s, (a i * a j) * ∫ x, f i x * f j x ∂μ =
        ∑ j ∈ s.erase i, (a i * a j) * ∫ x, f i x * f j x ∂μ +
        (a i * a i) * ∫ x, f i x * f i x ∂μ from
      (Finset.sum_erase_add s _ hi).symm]
  rw [show ∑ j ∈ s.erase i, (a i * a j) * ∫ x, f i x * f j x ∂μ = 0 from ?_]
  · -- Diagonal piece: (a i * a i) * ∫ f i * f i = (a i)^2 * ∫ (f i)^2
    rw [zero_add]
    have h_eq : ∀ x, f i x * f i x = (f i x) ^ 2 := fun x => by ring
    simp_rw [h_eq]
    congr 1
    ring
  · -- Off-diagonal vanishes
    apply Finset.sum_eq_zero
    intros j hj
    rw [Finset.mem_erase] at hj
    rw [h_orth i hi j hj.2 (Ne.symm hj.1), mul_zero]

/-! ## S3: cross-term orthogonality

Distinct `(k, j) ≠ (k', j')` give zero cross-expectation:
`∫ canonicalCrossTerm k j · canonicalCrossTerm k' j' ∂canonicalJointMeasure = 0`.

**Proof path** (deferred): the joint measure is `Measure.prod μ_S μ_R`
(see `FieldDecomposition.lean:47`), and the cross-term factorises as
`(smooth Wick monomial in η.1) · (rough Wick monomial in η.2)`. Apply
`MeasureTheory.integral_prod_mul` to split into a smooth integral
times a rough integral. Then the **2-site Wick power formula** (the
canonical analog of `gff_wickPower_two_site_inner`) gives a Kronecker
delta on each factor: smooth integral vanishes unless `j = j'`, rough
integral vanishes unless `k - j = k' - j'`. Combined: vanishes unless
`(k, j) = (k', j')`.

The 2-site Wick formula itself is the standard Janson-Hilbert
identity `∫ :φ(x)^n: :φ(y)^m: dμ = δ_{n,m} · n! · C(x,y)^n` for a
centered Gaussian field with covariance `C`. On the canonical side
this reduces (via `wickMonomial_pow_sum_expansion_of_totalDegree`
from gaussian-field) to multivariate Hermite orthogonality on the
standard product Gaussian (`hermiteMulti_orthogonality` from
gaussian-hilbert). Either provable in-repo or addable upstream.

S3 is the gating sorry for the L²-sq decomposition that S4 needs. -/

/-- **S3 (sorry'd): cross-term orthogonality.** Distinct `(k, j)` and
`(k', j')` give zero cross-expectation under the canonical joint
measure. Together with `MeasureTheory.integral_prod_mul`, this is the
one analytical input S4 needs from the Wick-orthogonality side.

See module docstring above for the proof sketch. -/
lemma canonicalCrossTerm_inner_eq_zero
    (T : ℝ) (k j k' j' : ℕ) (_h : (k, j) ≠ (k', j')) :
    ∫ η, canonicalCrossTerm d N a mass T η k j *
         canonicalCrossTerm d N a mass T η k' j'
         ∂(canonicalJointMeasure d N) = 0 := by
  sorry

/-! ## S3 application — `(c · binomial sum)`-style L²-sq decomposition

A shared helper that handles BOTH the leading `(1 / P.n)` piece and
each per-coefficient `P.coeff m` piece of `canonicalRoughError`: for any
fixed `(k, c)`, the L² norm of `c · Σ_j C(k, j) · cross(k, j)` decomposes
into the sum-of-squares form via the generic orthogonality reduction.

The leading-piece application is `k = P.n, c = 1 / P.n`; each
per-coefficient application is `k = m, c = P.coeff m` for `m : Fin P.n`.
The full per-coefficient sum (over `m`) is a further outer application
of the orthogonality reduction (left for follow-up). -/

/-- Generic helper: the L²-sq of `c · Σ_j C(k, j) · cross(k, j)`
decomposes into a sum of squared inner coefficients times squared L²
norms of the cross-terms. Both the leading piece and each per-coefficient
inner sum are special cases of this lemma. -/
lemma canonicalCrossTerm_scaled_inner_sum_l2_sq
    (T : ℝ) (k : ℕ) (c : ℝ)
    (h_int : ∀ j ∈ Finset.range k, ∀ j' ∈ Finset.range k,
        Integrable (fun η =>
            canonicalCrossTerm d N a mass T η k j *
            canonicalCrossTerm d N a mass T η k j')
            (canonicalJointMeasure d N)) :
    ∫ η, (c * ∑ j ∈ Finset.range k,
              (k.choose j : ℝ) * canonicalCrossTerm d N a mass T η k j) ^ 2
        ∂(canonicalJointMeasure d N) =
    ∑ j ∈ Finset.range k,
      (c * (k.choose j : ℝ)) ^ 2 *
        ∫ η, (canonicalCrossTerm d N a mass T η k j) ^ 2
            ∂(canonicalJointMeasure d N) := by
  -- Rewrite c · Σ_j ... as Σ_j (c · C(k, j)) · cross_j
  have h_pull : ∀ η, c * ∑ j ∈ Finset.range k,
        (k.choose j : ℝ) * canonicalCrossTerm d N a mass T η k j =
      ∑ j ∈ Finset.range k,
        (c * (k.choose j : ℝ)) *
          canonicalCrossTerm d N a mass T η k j := by
    intro η
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [h_pull]
  -- Apply the generic L²-orthogonality reduction
  apply integral_sq_real_sum_of_pairwise_orthogonal
    (Finset.range k)
    (fun j η => canonicalCrossTerm d N a mass T η k j)
    (fun j => c * (k.choose j : ℝ))
  · -- orthogonality: distinct j give zero cross-expectation (apply stub at k = k')
    intros j _ j' _ hne
    refine canonicalCrossTerm_inner_eq_zero d N a mass T k j k j' ?_
    intro h
    exact hne (congrArg Prod.snd h)
  · -- integrability hypothesis (pass through)
    exact h_int

/-- L²-sq decomposition of the leading `(1 / P.n)` piece of the rough
error. Direct application of `canonicalCrossTerm_scaled_inner_sum_l2_sq`
with `k = P.n` and `c = 1 / P.n`. -/
lemma canonicalRoughError_leading_l2_sq
    (T : ℝ) (P : InteractionPolynomial)
    (h_int : ∀ j ∈ Finset.range P.n, ∀ j' ∈ Finset.range P.n,
        Integrable (fun η =>
            canonicalCrossTerm d N a mass T η P.n j *
            canonicalCrossTerm d N a mass T η P.n j')
            (canonicalJointMeasure d N)) :
    ∫ η, ((1 / P.n : ℝ) * ∑ j ∈ Finset.range P.n,
              (P.n.choose j : ℝ) * canonicalCrossTerm d N a mass T η P.n j) ^ 2
        ∂(canonicalJointMeasure d N) =
    ∑ j ∈ Finset.range P.n,
      ((1 / P.n : ℝ) * (P.n.choose j : ℝ)) ^ 2 *
        ∫ η, (canonicalCrossTerm d N a mass T η P.n j) ^ 2
            ∂(canonicalJointMeasure d N) :=
  canonicalCrossTerm_scaled_inner_sum_l2_sq d N a mass T P.n (1 / P.n : ℝ) h_int

/-- L²-sq decomposition of a single per-coefficient `P.coeff m` piece
of the rough error (one fixed `m : Fin P.n`). Direct application of
`canonicalCrossTerm_scaled_inner_sum_l2_sq` with `k = m` and
`c = P.coeff m`. The full per-coefficient sum further sums these over
`m` (left for follow-up). -/
lemma canonicalRoughError_perCoeff_l2_sq
    (T : ℝ) (P : InteractionPolynomial) (m : Fin P.n)
    (h_int : ∀ j ∈ Finset.range (m : ℕ), ∀ j' ∈ Finset.range (m : ℕ),
        Integrable (fun η =>
            canonicalCrossTerm d N a mass T η (m : ℕ) j *
            canonicalCrossTerm d N a mass T η (m : ℕ) j')
            (canonicalJointMeasure d N)) :
    ∫ η, (P.coeff m * ∑ j ∈ Finset.range (m : ℕ),
              ((m : ℕ).choose j : ℝ) *
                canonicalCrossTerm d N a mass T η (m : ℕ) j) ^ 2
        ∂(canonicalJointMeasure d N) =
    ∑ j ∈ Finset.range (m : ℕ),
      (P.coeff m * ((m : ℕ).choose j : ℝ)) ^ 2 *
        ∫ η, (canonicalCrossTerm d N a mass T η (m : ℕ) j) ^ 2
            ∂(canonicalJointMeasure d N) :=
  canonicalCrossTerm_scaled_inner_sum_l2_sq d N a mass T (m : ℕ) (P.coeff m) h_int

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
