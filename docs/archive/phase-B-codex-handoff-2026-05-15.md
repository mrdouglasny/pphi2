# Phase B finish — codex handoff (2026-05-15)

**Branch:** `phase-b-discharge` (HEAD: `bbadd94`)
**Goal:** Convert the two textbook axioms in
`Pphi2/NelsonEstimate/CovarianceBoundsGJ.lean` to theorems by completing
Phases 1b, 2, 3, 4, 5 of the Phase B discharge.

This brief is self-contained for direct dispatch via `codex exec` or
similar. The rescue-agent path has been failing silently (returns fake
task IDs — `codex cloud list` confirms no real task exists). Run codex
manually from your terminal where TTY is available.

---

## What's already proved this session

In `Pphi2/NelsonEstimate/HeatKernelBound.lean`, `#print axioms` confirms
`[propext, Classical.choice, Quot.sound]` only on:

- **Phase 0** — `heat_kernel_1d_bound_uniform (L : ℝ) (hL : 0 < L)` (commit `70a484d`):
  `∃ C, 0 < C ∧ ∀ N [NeZero N] a (_ha : 0 < a) (_hvol : (N:ℝ)*a = L) t (_ht : 0 < t),
   Σ_{k ∈ range N} exp(-t·4·sin²(π·k/N)/a²) ≤ C·(1+1/√t)`.
- **Phase 1a** — `heat_kernel_trace_bound_uniform (d : ℕ) (L : ℝ) (hL : 0 < L) (mass : ℝ) (hmass : 0 < mass)` (commit `fda7ba6`):
  `∃ C, 0 < C ∧ ∀ N [NeZero N] a ha hvol t ht,
   Σ_{m ∈ range Λ} exp(-t·λ_m) ≤ C·(1+1/√t)^d · exp(-t·mass²)`.

Plus useful private helpers in HeatKernelBound.lean:

- `gaussian_sum_bound`, `sin_sq_lower_bound` (Jordan), `schwinger_smooth_Ioi`,
  `schwinger_rough` (Schwinger identities for both covariances)
- `latticeLaplacianEigenvalue_eq_sum`, `sum_finLatticeSites_prod`
  (factorization helpers used by Phase 1a)
- `sum_range_exp_neg_sq_le` (ℕ-version of `gaussian_sum_bound`)
- `sin_pi_div_N_reflect`, `pi_j_div_N_le_half_pi`, `sin_sq_pi_k_div_N_ge_min_sq`,
  `exp_neg_t_sin_sq_le` (per-term Phase 0 ingredients)
- `sum_min_le_two_sum` (sum-doubling lemma, antitone-required)

---

## Sister-repo context (already done; consume freely)

- **gaussian-hilbert**: zero local axioms (Workstream C complete this
  session). `polynomial_chaos_concentration` etc. depend only on
  `gross_lsi_implies_hypercontractive` + 3 markov-semigroups GaussianFin
  BE axioms (all upstream).
- **markov-semigroups**: Phase 2 Lp-carrier landed
  `GaussianFin.stdGaussianFin_dirichletMarkovSemigroup n :
   DirichletMarkovSemigroup (Fin n → ℝ)` on branch
  `feat/lp-carrier-stdGaussianFin-dirichletmarkov` (commit `6782dc7`).
  Don't worry about it for this work — pphi2 doesn't import
  markov-semigroups directly.

---

## Phase 1b — discharge `smoothWickConstant_le_log_uniform_in_aN`

**Theorem skeleton already in HeatKernelBound.lean** at line ~940
(`smoothWickConstant_le_log_uniform_in_aN_proved`). The witness is set:

```
A := 2 · L⁻¹^2 · C · (2 / mass^2 + 1)
B := 2 · L⁻¹^2 · C
```

where `C` is the Phase 1a `heat_kernel_trace_bound_uniform` constant for `d := 2`.

**Proof outline** (~150 lines):

1. **Schwinger:** rewrite each `smoothCovEigenvalue T m = exp(-T·λ_m)/λ_m`
   as `∫_T^∞ exp(-s·λ_m) ds` using the already-proved
   `schwinger_smooth_Ioi` (HeatKernelBound.lean:54).
2. **Sum-integral swap:** `Σ_m ∫_T^∞ exp(-s·λ_m) ds = ∫_T^∞ Σ_m exp(-s·λ_m) ds`.
   Use `MeasureTheory.integral_finset_sum` (or equivalent) for the
   finite-sum case.
3. **Volume identification:** `(a^d · Λ)⁻¹ = (a^d · N^d)⁻¹ = (Na)⁻ᵈ = L⁻ᵈ`,
   using `_hvol : (N:ℝ)*a = L` and `Fintype.card (FinLatticeSites d N) = N^d`.
4. **Apply Phase 1a:** `Σ_m exp(-s·λ_m) ≤ C · (1+1/√s)^d · exp(-s·mass²)`.
5. **Tighten** `(1+1/√s)² ≤ 2·(1+1/s)` (use `(1 - 1/√s)² ≥ 0`).
6. **Two integral bounds:**
   - `∫_T^∞ exp(-s·m²) ds = exp(-T·m²)/m² ≤ 1/m²` (uniform in T).
   - `∫_T^∞ (1/s)·exp(-s·m²) ds ≤ |log T| + 1/m²`, by case split on `T ≤ 1`
     vs `T > 1`:
     - `T ≤ 1`: `∫_T^∞ = ∫_T^1 + ∫_1^∞`. First bounded by `∫_T^1 1/s ds = -log T = |log T|`; second by `1/m²`.
     - `T > 1`: `(1/s)·exp(-s·m²) ≤ exp(-s·m²)`, integral `≤ 1/m² ≤ |log T| + 1/m²`.
7. **Combine:** total ≤ `2·L⁻²·C · (2/m² + |log T|)` ≤ `A + B·(1 + |log T|)`.

Math sketch is documented in the file as a comment block above the theorem.

**Mathlib helpers to look for:**
- `intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le` (FTC for `∫_T^∞`)
- `MeasureTheory.integral_Ioi_eq_integral_Ioc` style restatements
- `Real.exp_neg_mul_pos`, `Real.exp_le_one_iff` (positivity helpers)
- `Finset.sum_integral_eq_integral_sum` or the Mathlib equivalent

---

## Phase 2 — rough side, `m = 1`

For each `x : FinLatticeSites 2 N`:

```
a^d · Σ_y |C_R(x,y)| = a^d · Σ_y C_R(x,y)        [positivity of heat kernel]
                     = ∫_0^T (a^d · Σ_y p_s(x,y)) ds  [Schwinger, finite-sum Fubini]
                     = ∫_0^T exp(-s·mass²) ds      [constant function = m²-eigenvector]
                     = (1 - exp(-T·mass²))/mass² ≤ T  [`1 - exp(-x) ≤ x` for `x ≥ 0`]
```

The constant-function-as-mass²-eigenvector step needs the heat-kernel
normalization: `a^d · Σ_y (e^{-sM_a})(x, y) = exp(-s·mass²)`. Look for
this in `Pphi2/NelsonEstimate/FieldDecomposition.lean` (which has the
`canonicalRoughCovariance` definition). If not present, prove as a
private helper using:

- The Fourier-product basis `latticeFourierProductBasisFun` from
  `GaussianField/Lattice/LatticeFourierProduct.lean`.
- The constant function (k=0 in DFT) is the m²-eigenvector with
  eigenvalue `mass²`.

`canonicalRoughCovariance` definition:
```
def canonicalRoughCovariance (T : ℝ) (x y : FinLatticeSites d N) : ℝ :=
  (a^d : ℝ)⁻¹ * Σ_{m : Fin d → Fin N},
    canonicalRoughWeight d N a mass T m *
      latticeFourierProductBasisFun N d m x *
      latticeFourierProductBasisFun N d m y / ...
```

(See FieldDecomposition.lean:1554 for full definition.)

Estimated ~50-100 lines.

---

## Phase 3 — rough side, `m = 2` (Fubini + semigroup)

Per Gemini deep-think (verified 2026-05-12, see
`docs/phase-B-deep-think-record-2026-05-12.md`):

```
a²·Σ_y C_R(x,y)² = a²·Σ_y (∫_0^T p_s(x,y) ds)·(∫_0^T p_t(x,y) dt)
                 = ∫_0^T ∫_0^T (a²·Σ_y p_s(x,y)·p_t(x,y)) ds dt    [Fubini]
                 = ∫_0^T ∫_0^T p_{s+t}(x,x) ds dt                    [semigroup property]
```

The lattice semigroup identity `p_{s+t}(x,x) = a²·Σ_y p_s(x,y)·p_t(x,y)`
is the key. May need to prove as a private helper if not in
FieldDecomposition.lean.

Then:
- `p_{s+t}(x,x) = trace(e^{-(s+t)·M_a})/|Λ|` (by translation invariance —
  diagonal is x-independent on the torus).
- From Phase 1a: `trace ≤ C(L)·(1+1/√(s+t))² · exp(-(s+t)·m²) · |Λ|`.
- So `p_{s+t}(x,x) ≤ C(L)·(1+1/√(s+t))² · exp(-(s+t)·m²) ≤ C'(L)/(s+t)·exp(...)`.

The double integral closes exactly:
```
∫_0^T ∫_0^T 1/(s+t) ds dt = 2T·log(2T) - 2T·log(T) = (2 ln 2)·T
```

The `s·log(s) → 0` boundary term as `s → 0` is `Real.tendsto_self_mul_log_nhds_zero_zero`.

So `a²·Σ_y C_R(x,y)² ≤ (2 ln 2)·C'(L)·T`. Constant `C_2 := (2 ln 2)·C'(L)`.

Estimated ~200 lines.

---

## Phase 4 — rough side, `m ≥ 3` (Minkowski)

Use Minkowski integral inequality (commute ℓ^m INSIDE the s-integral):

```
(a²·Σ_y C_R(x,y)^m)^{1/m}
  = ‖∫_0^T p_s(x, ·) ds‖_{ℓ^m_y(a²)}
  ≤ ∫_0^T ‖p_s(x, ·)‖_{ℓ^m_y(a²)} ds       [Minkowski integral]
```

Bound the inner ℓ^m via Hölder on the spatial sum:

```
‖p_s‖_{ℓ^m}^m = a²·Σ_y p_s(x,y)^m
              ≤ ‖p_s‖_∞^{m-1} · (a²·Σ_y p_s(x,y))         [Hölder]
              = (C/s)^{m-1} · exp(-s·m²)                     [diagonal + stochastic norm]
              ≤ (C/s)^{m-1}.
```

So `‖p_s‖_{ℓ^m} ≤ C^{1-1/m} · s^{1/m - 1}`. The s-integral:

```
∫_0^T s^{1/m - 1} ds = m · T^{1/m}
```

Raising to the m-th power: `a²·Σ_y C_R(x,y)^m ≤ C^{m-1}·m^m·T`. Constant
`C_m := C(L)^{m-1}·m^m`.

For Mathlib's Minkowski integral inequality (counting measure on
`FinLatticeSites` integrated against Lebesgue on `[0, T]`): search for
`MeasureTheory.eLpNorm_integral_le_integral_eLpNorm` or
`Lp.norm_integral_le_integral_norm`. For the discrete counting-measure
case, a manual Cauchy-Schwarz / triangle inequality may be cleaner.

Estimated ~250 lines.

---

## Phase 5 — assembly

Convert both `axiom`s in `Pphi2/NelsonEstimate/CovarianceBoundsGJ.lean`
to `theorem`s using the proved versions from Phase 1b (smooth) and
Phases 2-4 (rough; combine via case-split on `m`).

```lean
theorem smoothWickConstant_le_log_uniform_in_aN
    {d : ℕ} (hd : d = 2) (mass L : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a)
        (_h_vol : (N : ℝ) * a = L)
        (T : ℝ) (_hT : 0 < T),
        smoothWickConstant d N a mass T ≤ A + B * (1 + |Real.log T|) :=
  smoothWickConstant_le_log_uniform_in_aN_proved hd mass L hL hmass

theorem canonicalRoughCovariance_pow_sum_le_uniform_in_aN
    {d : ℕ} (hd : d = 2) (mass L : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ C_m : ℝ, 0 < C_m ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a)
        (_h_vol : (N : ℝ) * a = L)
        (T : ℝ) (_hT : 0 < T) (x : FinLatticeSites d N),
        a^d * ∑ y : FinLatticeSites d N,
          |canonicalRoughCovariance d N a mass T x y| ^ m ≤ C_m * T := by
  subst hd
  rcases m with _ | _ | m
  · omega  -- contradicts hm
  · exact m1_case ...   -- Phase 2
  · -- m ≥ 2; either dispatch to Phase 3 (m=2) for tighter constant or
    -- straight to Phase 4 (m ≥ 2) for unified treatment.
    exact m_ge_2_case (m+2) ... -- Phase 4
```

After this lands, `#print axioms rough_error_variance` should show only
`[propext, Classical.choice, Quot.sound]` — the 2 Phase B textbook
axioms drop out automatically since downstream consumers reference
them by name.

Estimated ~50-100 lines.

---

## Acceptance criteria

1. `lake build` clean across all of pphi2 (currently 3163 jobs).
2. Both `axiom` declarations in `CovarianceBoundsGJ.lean` are `theorem`s.
3. `#print axioms rough_error_variance` shows ONLY `[propext, Classical.choice, Quot.sound]`.
4. Update `AXIOM_AUDIT.md`, `docs/AXIOM_STATUS.md`, `README.md`: pphi2 axiom count `19 → 17`.
5. Update `docs/phase-B-textbook-axioms.md` and
   `docs/T2-continuum-limit-status-2026-05-13.md` to mark Workstream A
   as ✅ COMPLETE.
6. Push commits to `phase-b-discharge`.

---

## Reference docs

- `docs/phase-B-codex-handoff-2026-05-12.md` — earlier handoff plan
  (pre-Phase-0/1a; Phase 0 helpers + 1a it spec'd are now DONE and live
  in `HeatKernelBound.lean`).
- `docs/phase-B-deep-think-record-2026-05-12.md` — Gemini deep-think
  proof sketches for Phases 3 + 4.
- `docs/phase-B-textbook-axioms.md` — original axiom proposal + Gemini
  DT vetting record.
- This session's commits to consult:
  - `27660f0` — Phase 0 helpers
  - `70a484d` — Phase 0 done (`heat_kernel_1d_bound_uniform`)
  - `0adf4d0` — Phase 1a helpers + skeleton
  - `fda7ba6` — Phase 1a done (`heat_kernel_trace_bound_uniform`)
  - `bbadd94` — Phase 1b skeleton (witness set, sketch documented)

## Estimated effort

~700 lines / ~7-10 active days (compared to original 1100 lines / 11.5 days
in the 2026-05-12 plan, after Phase 0 + 1a landing). Phases 2, 3, 4 are
each independent and can be parallelised.

## What NOT to touch

- gaussian-hilbert and markov-semigroups (Workstream C complete).
- `HeatKernelBound.lean` Phase 0 + 1a code (load-bearing primitives;
  consume only).
- pphi2 downstream consumer files (RoughErrorBound.lean already uses
  the axioms; `#print axioms` updates automatically once axioms become
  theorems).

## Dispatch suggestion (manual)

Run from your terminal (where TTY is available):

```sh
cd /Users/mdouglas/Documents/GitHub/pphi2
git worktree add /tmp/pphi2-phase-b-finish phase-b-discharge
cd /tmp/pphi2-phase-b-finish
codex exec "$(cat docs/phase-B-codex-handoff-2026-05-15.md)"
# or for cloud:
# codex cloud exec --env <env-id> "$(cat docs/phase-B-codex-handoff-2026-05-15.md)"
```

(The auto-dispatch through Claude's codex:codex-rescue agent has been
silently failing — it returns fake task IDs that don't appear in
`codex cloud list`. Manual dispatch from your terminal is the
workaround.)
