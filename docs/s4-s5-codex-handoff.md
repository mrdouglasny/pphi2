# S4 + S5 discharge — Codex hand-off

## Goal

Close the **last two pphi2 sorries** on the `rough_error_variance`
critical path, by introducing the two Gemini-vetted Phase B textbook
axioms (`docs/phase-B-textbook-axioms.md`) and using them to prove
S4 and S5.

Target end state: **pphi2 sorries 2 → 0**, **axioms 17 → 19**,
`rough_error_variance` proved modulo `[propext, Classical.choice,
Quot.sound]` + the two new textbook axioms.

## What's already in place

- ✅ S1, S2 proved axiom-free in `Pphi2/NelsonEstimate/RoughErrorBound.lean`.
- ✅ S3 main composition `canonicalRoughError_l2_sq_eq` (line 864)
  proved structurally — takes a bundle of orthogonality + integrability
  hypotheses, gives the L²-sq sum-of-squares form.
- ✅ S3 cross-term orthogonality `canonicalCrossTerm_inner_eq_zero`
  (line 407) proved axiom-free (you landed this).
- ✅ Canonical on-site variance identification in
  `Pphi2/NelsonEstimate/FieldDecomposition.lean`:
  `canonicalSmooth/RoughFieldFunction_self_moment_eq_smooth/RoughWickConstant`
  (you landed these too) — so the Wick subtraction constants
  `smoothWickConstant T` and `roughWickConstant T` are now provably
  the actual on-site variances of the smooth/rough fields.
- ✅ Off-diagonal marginal Wick lemmas
  `canonicalSmooth/RoughWickPower_two_site_marginal_eq_zero_of_ne` +
  integrability companions (you landed these for S3) — the `n ≠ m`
  case of the canonical 2-site Janson formula.
- ✅ Upstream gaussian-field primitives:
  `gff_wickPower_two_site_inner`, `multiWickMonomial_pi_gaussianReal_inner`,
  `gffPositionCovariance`.

## What's needed

### Two Phase B textbook axioms (corrected statements, Gemini-vetted)

Add in `Pphi2/NelsonEstimate/CovarianceSplit.lean` (or a new
`Pphi2/NelsonEstimate/CovarianceBoundsGJ.lean` if you prefer to isolate
the textbook-axiom block). Both restricted to `d = 2`, both with
quantifier order `∃ A B / ∃ C_m` outside `∀ N a T`:

```lean
/-- **Glimm-Jaffe Thm 8.5.2 (smooth-side, d=2).** Polylog T bound on
the smooth Wick constant, uniform in `(N, a)` at fixed `L = N · a`.
See `docs/phase-B-textbook-axioms.md` and `AXIOM_AUDIT.md` for the
discharge plan + Gemini DT vetting record. -/
axiom smoothWickConstant_le_log_uniform_in_aN
    {d : ℕ} (hd : d = 2) (mass L : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a)
        (_h_vol : (N : ℝ) * a = L)
        (T : ℝ) (_hT : 0 < T),
        smoothWickConstant d N a mass T ≤ A + B * (1 + |Real.log T|)

/-- **Glimm-Jaffe Thm 8.5.2 (rough-side, d=2).** Rough-covariance L^m
position-space site-sum bound (linear in T), for all `m ≥ 1`, uniform
in `(N, a)` at fixed `L = N · a`. See `docs/phase-B-textbook-axioms.md`
and `AXIOM_AUDIT.md` for the discharge plan + Gemini DT vetting. -/
axiom canonicalRoughCovariance_pow_sum_le_uniform_in_aN
    {d : ℕ} (hd : d = 2) (mass L : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ C_m : ℝ, 0 < C_m ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a)
        (_h_vol : (N : ℝ) * a = L)
        (T : ℝ) (_hT : 0 < T) (x : FinLatticeSites d N),
        a^d * ∑ y : FinLatticeSites d N,
          |canonicalRoughCovariance d N a mass T x y| ^ m ≤ C_m * T
```

Note `canonicalRoughCovariance d N a mass T x y` is a position-space
kernel currently not defined in the codebase. Add the def alongside
the axiom — mirroring `canonicalSmoothCovariance` if you've already
got that companion. Definition should be the diagonal of the
`(1 - exp(-T·M)) · M^{-1}` matrix in DFT-product basis, scaled by
`(a^d)^{-1}` (the Glimm-Jaffe-aligned scaling). Same form as
`canonicalSmoothFieldFunction_self_moment`'s RHS but with
`canonicalRoughWeight` instead of `canonicalSmoothWeight`.

### S4 discharge plan (use the axioms)

`canonicalCrossTerm_l2_sq_le` (line 985) after the d=2 + quantifier
fix is:
```lean
theorem canonicalCrossTerm_l2_sq_le
    {d : ℕ} (_hd : d = 2) (mass L : ℝ) (_hL : 0 < L) (_hmass : 0 < mass)
    (k j : ℕ) (_hkj : 1 ≤ k - j) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a)
        (_h_vol : (N : ℝ) * a = L)
        (T : ℝ) (_hT : 0 < T),
        ∫ η, (canonicalCrossTerm d N a mass T η k j) ^ 2
            ∂(canonicalJointMeasure d N) ≤
        K * T * (1 + |Real.log T|) ^ j := by sorry
```

**Proof:**

1. **Compute the diagonal `n = m` case of the 2-site formula.** Add a
   new lemma `canonicalCrossTerm_l2_sq_eq_covSum`:
   ```
   ∫ η, (cross(k, j))² dμ_joint = (a^d)² · j! · (k - j)! ·
     Σ_{x, y} C_S(x, y)^j · C_R(x, y)^{k - j}
   ```
   Same proof structure as `canonicalCrossTerm_inner_eq_zero` (line
   407, your existing proof) but on the diagonal — i.e., reuse the
   marginal Wick formulas but at `n = m` (which gives the Kronecker-
   diagonal `n! · C(x, y)^n` rather than zero). Will likely require
   adding diagonal marginal Wick lemmas
   `canonicalSmooth/RoughWickPower_two_site_marginal_eq_diagonal`
   analogous to the existing `_eq_zero_of_ne` siblings.

2. **Bound `|C_S(x, y)| ≤ smoothWickConstant T`.** Positive
   semidefiniteness of `canonicalSmoothCovariance` (kernel of a
   positive operator: `|C_S(x, y)| ≤ √(C_S(x, x) · C_S(y, y))`) + the
   variance identification you proved
   (`canonicalSmoothFieldFunction_self_moment_eq_smoothWickConstant`).
   Add as a small lemma.

3. **Apply Axiom 1**: `smoothWickConstant T ≤ A + B · (1 + |log T|)`,
   so `|C_S(x, y)|^j ≤ (A + B(1 + |log T|))^j ≤ (A + B)^j · (1 + |log T|)^j`
   (last step uses `A + B(1+|log T|) ≤ (A + B)(1+|log T|)` since
   `A · |log T| ≥ 0`).

4. **Apply Axiom 2** with `m = k - j ≥ 1` per the `_hkj` hypothesis:
   ```
   a^d · Σ_y |C_R(x, y)|^{k-j} ≤ C_{k-j} · T.
   ```

5. **Factor the position sum.** The outer `a^d · Σ_x` of constant
   gives `a^d · |Λ| = L^d`. Then:
   ```
   (a^d)² · Σ_{x, y} C_S^j · C_R^{k-j} ≤ (A+B)^j · (1+|log T|)^j · L^d · C_{k-j} · T
   ```

6. **Assemble `K`.** Take
   `K = j! · (k - j)! · L^d · max((A + B)^j · C_{k-j}, 1)`.
   The `max` with `1` ensures `K > 0` even in the degenerate
   `A = B = 0` case. Closes the `0 < K ∧ ...` existential.

### S5 discharge plan (use S3 + S4)

`rough_error_variance` (line 1024) after the d=2 + quantifier fix:
```lean
theorem rough_error_variance
    {d : ℕ} (_hd : d = 2) (P : InteractionPolynomial)
    (L mass : ℝ) (_hL : 0 < L) (_hmass : 0 < mass) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a)
        (_h_vol : (N : ℝ) * a = L)
        (T : ℝ) (_hT : 0 < T),
        ∫ η, (canonicalRoughError d N a mass T P η) ^ 2
          ∂(canonicalJointMeasure d N) ≤
        K * T * (1 + |Real.log T|) ^ (P.n - 1) := by sorry
```

**Proof:**

1. **Apply S3** (`canonicalRoughError_l2_sq_eq`, line 864) to
   express `∫ E_R² dμ` as the explicit sum-of-squares form (leading
   piece + Σ_m per-coefficient pieces). This requires discharging
   S3's integrability + orthogonality hypothesis bundle:
   - Orthogonality hypotheses: derive from
     `canonicalCrossTerm_inner_eq_zero` (line 407, already proved).
   - Integrability hypotheses: each `canonicalCrossTerm` is
     continuous in η (finite product/sum of polynomials of continuous
     evaluations), `canonicalJointMeasure` is a probability measure
     (finite), so apply `Continuous.integrable_of_isFiniteMeasure`
     for each. Add a small helper `canonicalCrossTerm_continuous`
     (mirror `gffMultiWickMonomial_orthogonality`'s in-file continuity
     argument).

2. **Apply S4** to each summand: for each `(k, j)` with `k ≤ P.n`
   and `j < k`, get `K_{k,j}` and `∫ cross(k, j)² ≤ K_{k,j} · T ·
   (1 + |log T|)^j`.

3. **Uniform polylog bound**: for `j ≤ P.n - 1` (since
   `j < k ≤ P.n` and `m = k - j ≥ 1`):
   `(1 + |log T|)^j ≤ (1 + |log T|)^(P.n - 1)` (since `1 + |log T| ≥ 1`).

4. **Sum**: the (k, j) index set has finite cardinality bounded by
   `P.n^2`. Sum the bounds:
   ```
   ∫ E_R² dμ ≤ (Σ_{(k, j)} coef_{k,j}^2 · K_{k,j}) · T · (1 + |log T|)^(P.n - 1)
   ```
   Take `K = max(Σ_{(k, j)} coef_{k,j}^2 · K_{k,j}, 1)`. Closes the
   existential.

## Acceptance criteria

- `lake build` clean.
- `#print axioms rough_error_variance` shows
  `[propext, Classical.choice, Quot.sound,
   smoothWickConstant_le_log_uniform_in_aN,
   canonicalRoughCovariance_pow_sum_le_uniform_in_aN]`.
- `#print axioms canonicalCrossTerm_l2_sq_le` similar.
- pphi2 sorry count in `RoughErrorBound.lean` drops to 0.
- No other new axioms; only the two named Phase B textbook ones.

## After landing

Update:
- `AXIOM_STATUS.md`: pphi2 axiom count 17 → 19; move the two new
  axioms out of the "proposed" subsection into the main inventory;
  sorry count 2 → 0.
- `AXIOM_AUDIT.md`: dated entry recording the introduction +
  discharge of S4 + S5.
- `README.md`: per-repo counts update.
- `docs/rough-error-variance-plan.md`: mark S4 + S5 as ✅.

## Estimated effort

Per recalibrated project norms: ~1-2 sessions of focused Lean work.
~300-500 lines net (positional covariance defs + diagonal marginal
Wick lemmas + S4 proof + S5 proof + integrability helpers).
