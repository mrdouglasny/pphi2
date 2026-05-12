# Phase B textbook axioms: closing S4 + S5 (rough_error_variance) sorries

## Goal

Formulate the **minimum** set of textbook axioms that, when introduced,
permits axiom-free (modulo the new textbook axioms) proofs of S4
(`canonicalCrossTerm_l2_sq_le`) and S5 (`rough_error_variance`), closing
the last two sorries on the `rough_error_variance` critical path.

These are **textbook axioms in the project sense** (per
`research-dev/library/lean/AXIOM_MANAGEMENT.md`): vetted statements of
standard results from Glimm-Jaffe / Reed-Simon / Janson with explicit
discharge plans, not "fundamental unprovable assumptions."

## Vetting record (Gemini deep-think, 2026-05-12)

Gemini deep-think vetting caught two bugs in the initial draft of this
doc:

1. **d = 2 trap (mathematical correctness).** Both axiom statements are
   **mathematically false for d ≥ 3.** In 2D the smooth Wick constant
   diverges logarithmically `~ log(1/T)` (matches Axiom 1), and the rough
   covariance L^m site-sum scales as exactly `T` for all `m ≥ 1` (matches
   Axiom 2). In 3D, the smooth Wick constant diverges as `T^{-1/2}`
   (power-law, not log), and the rough L^m bound has scaling
   `T^{m(1 - d/2) + d/2}` which diverges for `m ≥ 3` at `d = 3`. The
   linear-in-T scaling is a magical d=2 property (`m(1-1) + 1 = 1`).
   **Both axioms must carry `hd : d = 2`** to avoid an inconsistent
   axiomatization. Updated forms below.

2. **S4 quantifier trap.** In the previous S4 statement, `T` was bound
   *before* `∃ K`, so Lean's elimination allows `K` to be a function of
   `T` (Skolemization). A discharge could then pick `K(T) = 1/T`,
   completely nullifying the `O(T · polylog T)` variance scaling needed
   by S5. **`T` must be moved inside the `∀ N a` block** so `K` is forced
   to be a function only of `(k, j, mass, L)`. Same trap was present in
   S5; same fix.

Verdict on the underlying math: "very well-thought-out formalization
strategy. The split between the L^∞ bound on the smooth covariance and
the L^m bound on the rough covariance perfectly mirrors the standard
analytic strategy (Glimm-Jaffe / Simon)." All four (a)–(d) criteria are
met for both axioms in their corrected forms below. The two axioms are
correct, sufficient, and well-split (don't merge them).

## The two textbook axioms

Both go in `Pphi2/NelsonEstimate/CovarianceSplit.lean` (or a new
`Pphi2/NelsonEstimate/CovarianceBoundsGJ.lean` if you prefer to isolate
the Phase B Fourier estimates).

### Axiom 1: `(a, N)`-uniform smooth-Wick-constant log bound

```lean
/-- **Glimm-Jaffe Theorem 8.5.2 (smooth-side).** The smooth Wick constant
`c_S = smoothWickConstant T` is bounded by a polylog of T uniformly in
the lattice discretisation `(N, a)` at fixed macroscopic period
`L = N · a`.

  `smoothWickConstant d N a mass T ≤ A + B · (1 + |log T|)`

with `A, B` depending only on `(d, mass, L)`. The textbook proof uses
sharper lattice Fourier estimates (`heat_kernel_1d_bound` with the
`(a, N)`-uniform `C(L)` constant — currently only the trivial
`C = N` form is in the codebase) plus the Schwinger integral identity
for `c_S = ∫_T^∞ trace(e^{-t·M_a}/|Λ|) dt` and the lattice-torus
heat kernel bound `trace(e^{-t·M_a})/|Λ| ≤ const · min(1/(t·m²), 1/t)`.

**Reference:** Glimm-Jaffe, *Quantum Physics: A Functional Integral
Point of View*, 2nd ed., Theorem 8.5.2 + Lemma 8.5.4 (lattice heat
kernel trace bound); Reed-Simon vol. II, Theorem XI.2 (heat kernel
trace).

**Discharge strategy:** prove the `(a, N)`-uniform `heat_kernel_1d_bound`
via the standard Gaussian-sum bound on `Σ_k exp(-t·4·sin²(πk/N)/a²) ≤
C·(1 + 1/√t)` with `C` depending only on `L` (the existing
`heat_kernel_1d_bound` proves this with `C = N`, the wrong shape). Apply
in `d` dimensions via tensor-product factorisation and the Schwinger
integral. The argument is several hundred lines of careful Fourier
analysis but standard.

**Vetting:** Standard. -/
axiom smoothWickConstant_le_log_uniform_in_aN
    {d : ℕ} (hd : d = 2) (mass L : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a)
        (_h_vol : (N : ℝ) * a = L)
        (T : ℝ) (_hT : 0 < T),
        smoothWickConstant d N a mass T ≤ A + B * (1 + |Real.log T|)
```

### Axiom 2: `(a, N)`-uniform rough covariance L^m summability

```lean
/-- **Glimm-Jaffe Theorem 8.5.2 (rough-side).** For each `m ≥ 1`, the
`m`-th-power site-sum of the rough covariance is bounded by a constant
times `T`, uniformly in the lattice discretisation `(N, a)` at fixed
macroscopic period `L = N · a`.

  `a^d · Σ_y |C_R(x, y)|^m ≤ C_m · T`

with `C_m` depending only on `(d, mass, L, m)`. The existing
`roughCovariance_sq_summable` is the `m = 2` case (and even then in
spectral, not position-space, form); this axiom extends to all `m ≥ 1`
and uses position-space sums.

**Reference:** Glimm-Jaffe, *Quantum Physics*, 2nd ed., Theorem 8.5.2 +
Lemma 8.5.5 (rough covariance position-space estimates); Janson,
*Gaussian Hilbert Spaces*, Ch. 6 (Wick chaos hypercontractivity input).

**Math content:**
* `m = 1`: rough covariance has spatial integral exactly `T`
  (Schwinger: `a^d · Σ_y C_R(x, y) = ∫_0^T 1 dt = T` by the heat kernel
  probabilistic normalization `a^d · Σ_y p_t(x, y) = 1`).
* `m = 2`: position-space form of `roughCovariance_sq_summable`
  (Plancherel: `Σ_{x,y} C_R(x,y)² = Σ_k |Ĉ_R(k)|² ≤ |Λ| · T · a^d · c_a
  ≤ |Λ| · T / mass²`; divide by `|Λ|` and use translation
  invariance).
* `m ≥ 3`: in d=2 the continuum singularity is `(-log|x|)^m`, which is
  locally integrable. The lattice estimate then mirrors the continuum
  bound. Direct via Hölder + the `m = 2` and `m = ∞` (i.e. local
  boundedness away from `x = y`) cases, or via the explicit heat-kernel
  formula `C_R(x, y) = ∫_0^T p_t(x, y) dt` and pointwise heat-kernel
  Gaussian bounds.

**Discharge strategy:** prove `m = 1` directly from the Schwinger
identity + heat-kernel probability normalisation. Prove `m = 2`
in position-space form by Plancherel + `roughCovariance_sq_summable`.
Prove `m ≥ 3` by Hölder interpolation between `m = 2` and the `L^∞`
bound on `C_R` for `x ≠ y` (the `x = y` term contributes negligibly
because `(a^d) · C_R(x,x)^m ≤ a^d · (log(1/a))^m → 0` as `a → 0` in
d ≥ 2).

**Vetting:** Standard. -/
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

(`canonicalRoughCovariance d N a mass T x y` is the position-space
covariance kernel of the rough field, parallel to the already-defined
`canonicalSmoothCovariance` companion in `FieldDecomposition.lean`'s
post-refactor state. If not yet defined, add as a small `def`
mirroring the smooth side — the definition is the position-space
matrix entry of `(1 - exp(-T·M)) · M^{-1}` scaled by `(a^d)^{-1}`.)

## How these close S4 + S5

### S4 (`canonicalCrossTerm_l2_sq_le`)

**Statement.** For `(k, j)` with `1 ≤ k - j` and `k ≤ P.n`, there
exists `K > 0` such that for all `(N, a)` with `N · a = L`:
```
∫ η, (canonicalCrossTerm d N a mass T η k j)² ∂(canonicalJointMeasure d N)
  ≤ K · T · (1 + |log T|)^j
```

**Proof using axioms 1 + 2:**

1. **Compute the L² norm via S3-style 2-site formulas.** From the
   already-landed canonical marginal Wick formulas:
   ```
   ∫ η, cross(k, j)² dμ_joint
     = (a^d)² · Σ_{x,y}
         (j! · canonicalSmoothCovariance(x, y)^j) ·
         ((k - j)! · canonicalRoughCovariance(x, y)^{k - j}).
   ```
   This step is the diagonal `n = m` case of the canonical 2-site
   Janson formula. Same proof shape as `canonicalCrossTerm_inner_eq_zero`
   (just lands on the diagonal). Add as a separate lemma
   `canonicalCrossTerm_l2_sq_eq_covSum`. Mechanical — same primitives
   used by S3.

2. **Bound the smooth-covariance factor.**
   `|canonicalSmoothCovariance(x, y)| ≤ smoothWickConstant T` (positive
   semidefiniteness: `|C_S(x,y)| ≤ √(C_S(x,x) · C_S(y,y)) =
   smoothWickConstant T` by translation invariance, which Codex already
   landed in `FieldDecomposition.lean`). Then **apply Axiom 1**:
   ```
   |C_S(x, y)|^j ≤ (smoothWickConstant T)^j ≤ (A + B(1 + |log T|))^j.
   ```

3. **Bound the rough-covariance factor + position sum.**
   The position sum factorises as `Σ_{x,y} ... = a^d Σ_x · a^d Σ_y · ...`
   and the rough piece is bounded by **Axiom 2** with `m = k - j ≥ 1`:
   ```
   a^d · Σ_y |C_R(x, y)|^{k - j} ≤ C_{k-j} · T.
   ```
   The outer `a^d · Σ_x` of the constant smooth-bound term is `L^d`.

4. **Combine.** The constant is
   ```
   K = j! · (k - j)! · L^d · (A + B(1 + max_T(|log T|)))^j · C_{k-j} / (max polylog factor)
   ```
   — actually cleaner to absorb the polylog factor into the RHS form:
   ```
   ∫ cross² dμ ≤ j! · (k-j)! · L^d · C_{k-j} · (A + B + B|log T|)^j · T
              ≤ K · T · (1 + |log T|)^j
   ```
   for `K = j! · (k-j)! · L^d · C_{k-j} · max(A+B, B)^j` (absorbing the
   trivial `1` and polylog into the j-th power). Existential closes S4.

**Net.** S4 is a few hundred lines of arithmetic + the new
`canonicalCrossTerm_l2_sq_eq_covSum` lemma. No new analytical content
beyond the two textbook axioms.

### S5 (`rough_error_variance`)

**Statement.** For any `InteractionPolynomial P`, there exists
`K(P, mass, L) > 0` such that for all `(N, a)` with `N · a = L`:
```
∫ η, (canonicalRoughError d N a mass T P η)² ∂(canonicalJointMeasure d N)
  ≤ K · T · (1 + |log T|)^(P.n - 1).
```

**Proof using S3 + S4 (axiom-free given S4):**

1. **Apply S3** (`canonicalRoughError_l2_sq_eq`, already proved): the
   LHS decomposes into the leading sum-of-squares plus the
   per-coefficient sum-of-squares.

2. **Apply S4** to each summand: for each `(k, j)` with `k ≤ P.n` and
   `j < k`, get a bound `∫ cross(k, j)² ≤ K_{k,j} · T · (1 + |log T|)^j`.

3. **Use `j ≤ P.n - 1`** (since `j < k ≤ P.n` and `m = k - j ≥ 1`) to
   uniformly bound the polylog exponent:
   `(1 + |log T|)^j ≤ (1 + |log T|)^(P.n - 1)`
   (assuming `1 + |log T| ≥ 1`, which holds since `|log T| ≥ 0`).

4. **Sum the finite (k, j) terms** into the final `K(P, mass, L) =
   Σ_{(k,j)} (coef_{k,j})² · K_{k,j}`. The sum is over a finite index
   set bounded by `P.n` — closes the existential.

5. **Discharge the integrability hypotheses** of S3
   (`canonicalRoughError_l2_sq_eq` takes integrability bundles). Each
   `canonicalCrossTerm` is continuous in `η` (finite product/sum of
   continuous functions), `canonicalJointMeasure` is a probability
   measure (hence finite), so each `canonicalCrossTerm² dμ` is
   integrable via `Continuous.integrable_of_isFiniteMeasure`. Similarly
   for the cross-products. This is mechanical Mathlib bookkeeping
   (no analytical content) and can be packaged as a small
   `canonicalCrossTerm_continuous` helper (~30 lines) + a couple of
   `Integrable.mul` / `Integrable.const_mul` chains.

**Net.** S5 is a routine assembly given S3 + S4 + the integrability
helpers. No further axioms needed.

## Discharge / vetting plans for the axioms

Both axioms are textbook results (Glimm-Jaffe Ch. 8). Discharge plan:

- **Axiom 1** (`smoothWickConstant_le_log_uniform_in_aN`): tighten the
  existing `heat_kernel_1d_bound` (currently with `C = N`) to the
  textbook `(a, N)`-uniform `C = C(L)` form via the standard
  Gaussian-sum bound (`gaussian_sum_bound` in
  `Pphi2/NelsonEstimate/HeatKernelBound.lean:204` already proves the
  `(a, N)`-uniform `Σ exp(-α k²) ≤ √(π/α) + 1` — apply this via
  `sin² ≥ (2/π)² · x²` for x ∈ [0, π/2]). Then propagate through
  `heat_kernel_trace_bound`, `smoothVariance_from_heat_kernel`,
  `smoothVariance_le_log_uniform`. Estimated: ~500-800 lines, ~2-3 weeks.

- **Axiom 2** (`canonicalRoughCovariance_pow_sum_le_uniform_in_aN`): the
  m=1 case is the Schwinger-identity computation
  (`a^d Σ_y C_R(x, y) = ∫_0^T 1 dt = T`); m=2 is a position-space
  rewrite of the existing `roughCovariance_sq_summable`; m≥3 follows
  from Hölder interpolation between m=2 and L^∞ bounds on the
  off-diagonal heat kernel (which decay Gaussian-exponentially in
  |x - y|, dominating any logarithmic divergence at coincident points
  in d=2). Estimated: ~300-500 lines, ~1-2 weeks.

Combined Phase B effort: ~3-5 weeks at recalibrated norms. The pphi2
audit table tracks these as standard textbook axioms with full
discharge plans (per the
`research-dev/library/lean/AXIOM_MANAGEMENT.md` protocol).

## Net effect on sorry / axiom inventory

Before:
* pphi2 axioms: 17 (15 public + 2 private)
* pphi2 sorries: 2 (S4 + S5 in `RoughErrorBound.lean`)
* gaussian-field axioms: 3

After introducing the two textbook axioms and proving S4 + S5:
* pphi2 axioms: 19 (17 prior + 2 new textbook = 19 actual, `count_axioms.sh`
  would report 21 due to docstring false positives)
* pphi2 sorries: 0
* gaussian-field axioms: 3

The two new axioms displace the two sorries, with the trade favouring
audit-trackable textbook axioms over open sorries: the axioms are
named, cited, with discharge plans, and have verifiable mathematical
content per the project's textbook-axiom protocol.

## Net effect on `polynomial_chaos_exp_moment_bridge`

With S4 + S5 closed via the two new textbook axioms, `rough_error_variance`
is proved (modulo `[propext, Classical.choice, Quot.sound]` + the two
new textbook axioms). This is **Step 1** of the full bridge axiom
discharge. The next steps (Janson 5.10 application for L^p and tail
bounds, layer-cake / dynamical-cutoff assembly) are described in
`polynomial-chaos-exp-moment-bridge-proof-plan.md`. None of those add
new axioms beyond `polynomial_chaos_concentration` (already a theorem
in gaussian-hilbert, axiom-free).

So **the introduction of these two textbook axioms unlocks the entire
`rough_error_variance` proof**, leaving only Phase 2/3 (Lp + tail +
assembly) as the remaining work to discharge the full
`polynomial_chaos_exp_moment_bridge` axiom — which is itself the
critical-path axiom for the T² interacting OS theorem.
