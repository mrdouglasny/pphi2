# Canonical 2-site Wick formula -> S3 discharge

## Status

S3 is now discharged in
`Pphi2/NelsonEstimate/RoughErrorBound.lean`.

The proved theorem is:

```lean
lemma canonicalCrossTerm_inner_eq_zero
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (k j k' j' : ℕ)
    (hj : j ∈ Finset.range k) (hj' : j' ∈ Finset.range k')
    (h : (k, j) ≠ (k', j')) :
    ∫ η, canonicalCrossTerm d N a mass T η k j *
         canonicalCrossTerm d N a mass T η k' j'
         ∂(canonicalJointMeasure d N) = 0
```

This removes the S3 sorry and unblocks the formal L² decomposition step
`canonicalRoughError_l2_sq_eq`.

## Variance Identification Prerequisite

The prerequisite in
`docs/canonical-variance-identification-discharge-plan.md` is complete.
`FieldDecomposition.lean` now proves, axiom-free:

1. `canonicalSmoothFieldFunction_self_moment_const`
2. `canonicalSmoothFieldFunction_self_moment_eq_smoothWickConstant`
3. `canonicalRoughFieldFunction_self_moment_eq_roughWickConstant`

These are the matched-variance facts needed for canonical Wick
orthogonality.

## What Landed

The actual discharge route stayed inside `pphi2`; no upstream
`gaussian-field` generalization was required.

In `Pphi2/NelsonEstimate/FieldDecomposition.lean`:

1. Added canonical marginal field views
   `canonicalSmoothFieldFunctionOfFst` and
   `canonicalRoughFieldFunctionOfSnd`.
2. Proved integrability of the two-site marginal Wick products:
   `canonicalSmoothWickPower_two_site_marginal_integrable` and
   `canonicalRoughWickPower_two_site_marginal_integrable`.
3. Proved off-diagonal degree orthogonality on the canonical product
   Gaussian marginals:
   `canonicalSmoothWickPower_two_site_marginal_eq_zero_of_ne` and
   `canonicalRoughWickPower_two_site_marginal_eq_zero_of_ne`.

The proofs use:

1. `wickMonomial_pow_sum_expansion_of_totalDegree`
2. `multiWickMonomial_pi_gaussianReal_inner`
3. the variance-identification lemmas above

In `Pphi2/NelsonEstimate/RoughErrorBound.lean`, S3 is discharged by:

1. expanding the product of two `canonicalCrossTerm`s into a finite
   double site sum,
2. factoring each summand across the smooth and rough Gaussian
   coordinates using `MeasureTheory.integral_prod_mul`, and
3. killing each summand by smooth-degree mismatch or rough-degree
   mismatch.

## Why The Extra Hypotheses Appear

The final theorem statement carries:

1. `ha : 0 < a`
2. `hmass : 0 < mass`
3. `hT : 0 < T`
4. `hj : j ∈ Finset.range k`
5. `hj' : j' ∈ Finset.range k'`

These are not cosmetic. They are used to:

1. invoke the canonical marginal integrability and Wick orthogonality
   lemmas,
2. identify the Wick subtraction constants with the actual marginal
   variances, and
3. derive `k - j ≠ k' - j'` from `(k, j) ≠ (k', j')` when `j = j'`.

## Next Blocker

The active blocker is now S4:

```lean
theorem canonicalCrossTerm_l2_sq_le ... := by
  sorry
```

This still needs the Phase B Glimm-Jaffe analytic inputs cited in
`docs/rough-error-variance-plan.md`:

1. an `(a, N)`-uniform smooth covariance bound of the form
   `canonicalSmoothCovariance_le_log`, and
2. an `(a, N)`-uniform rough covariance L^m summability bound of the
   form `canonicalRoughCovariance_pow_sum_le` for all `m >= 1`.

At the moment the codebase only has weaker or narrower substitutes:

1. `smoothVariance_le_log_uniform`, whose constant still depends on `a`,
   and
2. `roughCovariance_sq_summable`, which only covers the `m = 2` case.

So S4 is genuinely upstream-blocked; S3 is not.

## Acceptance Record

Completed:

1. `canonicalCrossTerm_inner_eq_zero` proved.
2. `lake build Pphi2.NelsonEstimate.RoughErrorBound` succeeds.
3. pphi2 sorry count in `RoughErrorBound.lean` drops from S3+S4+S5 to
   just S4+S5.

Remaining:

1. `canonicalCrossTerm_l2_sq_le` (S4)
2. `rough_error_variance` (S5 assembly)
