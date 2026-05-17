# Phase B discharge — codex handoff (2026-05-12)

**Branch:** `phase-b-discharge` (off `audit/migrate-and-refresh`, PR #17)
**Last commit:** `27660f0` (Phase 0 helpers landed, 2 sorries documented)
**Goal:** Convert two textbook axioms in `Pphi2/NelsonEstimate/CovarianceBoundsGJ.lean`
to theorems:
1. `smoothWickConstant_le_log_uniform_in_aN`
2. `canonicalRoughCovariance_pow_sum_le_uniform_in_aN`

**Strategy fully verified by Gemini deep-think on 2026-05-12** —
see `docs/phase-B-deep-think-record-2026-05-12.md` for the proof
sketches. **No log corrections needed; both axioms collapse onto a
single `(a, N)`-uniform heat-kernel sum upgrade.**

---

## Status of work in progress

**Helpers landed, compiling cleanly** (`Pphi2/NelsonEstimate/HeatKernelBound.lean`,
`section UniformBound`, lines 393–600):
- `sin_pi_div_N_reflect (N k : ℕ) (hk : k ≤ N)` — reflection formula
  `sin(π·k/N) = sin(π·(N-k)/N)`.
- `pi_j_div_N_le_half_pi`, `pi_j_div_N_nonneg` — `π·j/N ∈ [0, π/2]` for
  `j = min(k, N-k)`.
- `sin_sq_pi_k_div_N_ge_min_sq` — pointwise bound
  `(2j/N)² ≤ sin²(π·k/N)` via Jordan's inequality.
- `exp_neg_t_sin_sq_le` — per-term bound
  `exp(-t·4sin²(πk/N)/a²) ≤ exp(-16t·j(k)²/L²)` using `L = N·a` to
  absorb the lattice-spacing dependence. **The key load-bearing lemma.**

**Two sorries to fill**:

### Sorry 1: `sum_min_le_two_sum` (HeatKernelBound.lean ~line 552)

Statement:
```lean
private lemma sum_min_le_two_sum (N : ℕ) (g : ℕ → ℝ) (hg : ∀ j, 0 ≤ g j) :
    (∑ k ∈ range N, g (min k (N - k))) ≤ 2 * ∑ j ∈ range N, g j
```

The pointwise bound `g(min k (N-k)) ≤ g(k) + g(N-k)` is already filled in
(uses `Nat.min_eq_left`/`Nat.min_eq_right`). What remains is showing
`∑_{k ∈ range N} g(N-k) ≤ ∑_{k ∈ range N} g(k)`.

**Strategy:** This is NOT generally true pointwise — `N - k` for `k ∈ {0, ..., N-1}`
ranges over `{1, ..., N}`, so the sums differ at the endpoints (`g(0)` on the
left, `g(N)` on the right). Use one of:

- **(Easiest)** Use `Finset.sum_range_reflect` directly:
  ```
  ∑_{k ∈ range N} g(N-1-k) = ∑_{k ∈ range N} g(k).
  ```
  Then bound `g(N-k) ≤ g(N-1-k) + g(0)`... no, that's not clean either.

- **(Cleanest)** Split off the `k = 0` term:
  `∑_{k ∈ range N} g(N-k) = g(N) + ∑_{k ∈ Ioo 0 N} g(N-k) = g(N) + ∑_{j ∈ Ioo 0 N} g(j)`
  (re-indexing `j = N - k` for `k ∈ {1, ..., N-1}` gives `j ∈ {1, ..., N-1}`).
  And `∑_{k ∈ range N} g(k) = g(0) + ∑_{j ∈ Ioo 0 N} g(j)`. So both sums differ
  by `g(N) − g(0)`, which is NOT controllable in general.

- **(Workaround — change the statement)** Strengthen the hypothesis to
  `g antitone` (which is what we need: `g(j) = exp(-α·j²)` is decreasing in `j ≥ 0`).
  Then `g(N) ≤ g(0)` trivially.

**Recommended fix**: change the lemma signature to require `g` antitone:
```lean
private lemma sum_min_le_two_sum (N : ℕ) (g : ℕ → ℝ)
    (hg : ∀ j, 0 ≤ g j) (h_anti : Antitone g) :
    (∑ k ∈ range N, g (min k (N - k))) ≤ 2 * ∑ j ∈ range N, g j
```
Then `g(N-k) ≤ g(0)` etc.

Even simpler: directly bound `g(N-k) ≤ g(if k = 0 then 0 else N-k)` — no, still
awkward.

**Best**: use `Finset.sum_image_le` or direct sum-bijection:

```lean
have : ∑ k ∈ range N, g (N - k) =
       g N + ∑ k ∈ Finset.Ioo 0 N, g (N - k) := by ...  -- split off k=0
have h_reindex : ∑ k ∈ Finset.Ioo 0 N, g (N - k) =
                 ∑ j ∈ Finset.Ioo 0 N, g j := by
  -- bijection k ↦ N - k from Ioo 0 N to itself
  ...
```

Then `RHS = g(N) + ∑_{j=1}^{N-1} g(j) ≤ g(0) + ∑_{j=1}^{N-1} g(j) = ∑_{j=0}^{N-1} g(j)`
provided `g(N) ≤ g(0)` — which DOES hold for our application
(`g(j) = exp(-α·j²)`, decreasing) and any antitone `g`.

**Cleanest path**: make `g` antitone in the signature.

### Sorry 2: `heat_kernel_1d_bound_uniform` (HeatKernelBound.lean ~line 594)

Statement:
```lean
theorem heat_kernel_1d_bound_uniform (L : ℝ) (hL : 0 < L) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a) (_hvol : (N : ℝ) * a = L)
      (t : ℝ) (_ht : 0 < t),
      (∑ k ∈ range N,
        exp (-t * (4 * Real.sin (π * (k : ℝ) / N) ^ 2 / a ^ 2)) : ℝ) ≤
      C * (1 + 1 / Real.sqrt t)
```

Witness: `C(L) = L · √π / 2 + 2` (worked out below). Step 1 (per-term
bound via `exp_neg_t_sin_sq_le`) is filled. Steps 2–5 are the sorry.

**Step 2:** Apply `sum_min_le_two_sum` (after fixing Sorry 1) with
`g(j) := exp(-(16t/L²)·j²)`. This `g` is antitone (decreasing in `j`).

```lean
have step2 : ∑ k ∈ range N, exp (-(16 * t) * (min k (N-k) : ℝ)^2 / L^2) ≤
             2 * ∑ j ∈ range N, exp (-(16 * t) * (j : ℝ)^2 / L^2) := by
  apply sum_min_le_two_sum
  · intro j; exact (Real.exp_pos _).le
  · -- Antitonicity of j ↦ exp(-α·j²) on ℕ.
    intro j₁ j₂ hj
    apply Real.exp_le_exp.mpr
    have : (j₁ : ℝ)^2 ≤ (j₂ : ℝ)^2 := by
      apply sq_le_sq' <;> [linarith [Nat.cast_nonneg j₁]; exact_mod_cast hj]
    nlinarith [sq_nonneg ((j₂ : ℝ)), sq_nonneg ((j₁ : ℝ)),
               (by positivity : (0:ℝ) ≤ 16*t/L^2)]
```

**Step 3:** Embed nonneg sum in the symmetric Z-sum:

```lean
have step3 : ∑ j ∈ range N, exp (-(16 * t) * (j : ℝ)^2 / L^2) ≤
             ∑ k ∈ Finset.Icc (-((N - 1 : ℕ) : ℤ)) ((N - 1 : ℕ) : ℤ),
               exp (-(16 * t / L^2) * (k : ℝ)^2) := by
  -- The map j : ℕ ↦ (j : ℤ) embeds range N into Icc (-(N-1)) (N-1).
  -- Use Finset.sum_image_le or sum_le_sum_of_subset.
  sorry  -- subgoal for codex
```

Or even simpler, use `Finset.sum_Icc_consecutive` or similar. The cleanest:
prove `range N` (ℕ-sum) ≤ `Icc 0 (N-1)` (ℤ-sum) ≤ `Icc (-(N-1)) (N-1)` (ℤ-sum).

**Step 4:** Apply `gaussian_sum_bound` with `α := 16t/L²` and `M := N-1`:

```lean
have step4 := gaussian_sum_bound (16 * t / L^2) (by positivity) (N - 1)
-- step4 : Σ_{k ∈ Icc (-(N-1)) (N-1)} exp(-α·k²) ≤ 1 + sqrt(π/α)
-- α = 16t/L², so sqrt(π/α) = sqrt(πL²/(16t)) = L · sqrt(π) / (4 · sqrt t).
```

**Step 5:** Combine and arithmetic. With `C(L) = L·√π/2 + 2`:

```
2 · (1 + L·√π/(4·√t)) = 2 + L·√π/(2·√t)
                     ≤ (L·√π/2) · (1/√t) + 2 · 1
                     = (L·√π/2 + 2) · (1 + 1/√t) - (L·√π/2 + 2/√t) + ...
```

Wait, the cleanest arithmetic: want to show
`2 + L·√π/(2·√t) ≤ (L·√π/2 + 2) · (1 + 1/√t)`.

Expand RHS: `(L·√π/2 + 2) + (L·√π/2 + 2)/√t = (L·√π/2 + 2) + (L·√π/2)/√t + 2/√t`.

So RHS − LHS = `(L·√π/2 + 2) + L·√π/(2·√t) + 2/√t − 2 − L·√π/(2·√t)`
            = `L·√π/2 + 2/√t ≥ 0` ✓.

This is a `nlinarith` after the substitution. Or use `positivity` with the
right setup.

---

## Phase 1: smooth-side axiom (≈100 lines)

Need to upgrade `heat_kernel_trace_bound` to `(a, N)`-uniform form, then
integrate `c_S = ∫_T^∞ trace(e^{-sM_a})/|Λ| ds` to get the polylog T bound.

### Phase 1a: upgrade `heat_kernel_trace_bound`

Add a new theorem `heat_kernel_trace_bound_uniform`:

```lean
theorem heat_kernel_trace_bound_uniform (d : ℕ) (L : ℝ) (hL : 0 < L)
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a) (_hvol : (N : ℝ) * a = L)
      (t : ℝ) (_ht : 0 < t),
      (∑ m ∈ range (Fintype.card (FinLatticeSites d N)),
        exp (-t * latticeEigenvalue d N a mass m) : ℝ) ≤
      C * (1 + 1 / Real.sqrt t) ^ d * Real.exp (-t * mass^2)
```

**Proof:** The eigenvalues are `λ_m = mass² + Σ_{i=1}^d 4·sin²(π·k_i/N)/a²`
where `m ↔ (k_1, ..., k_d) ∈ (Fin N)^d`. The sum factorizes:

```
Σ_m exp(-t·λ_m) = exp(-t·mass²) · ∏_{i=1}^d Σ_{k_i} exp(-t·4sin²(πk_i/N)/a²)
                ≤ exp(-t·mass²) · (C(L) · (1 + 1/√t))^d
```

Need to find `latticeEigenvalue_eq` and the tensor-product structure in
`Pphi2/NelsonEstimate/HeatKernelBound.lean` or `CovarianceSplit.lean`.
`Fintype.card (FinLatticeSites d N) = N^d` and the sum re-indexes through
`Finset.prod_univ_pi` / `Fintype.sum_pi_finset`.

### Phase 1b: discharge `smoothWickConstant_le_log_uniform_in_aN`

```lean
theorem smoothWickConstant_le_log_uniform_in_aN
    {d : ℕ} (hd : d = 2) (mass L : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a)
        (_h_vol : (N : ℝ) * a = L)
        (T : ℝ) (_hT : 0 < T),
        smoothWickConstant d N a mass T ≤ A + B * (1 + |Real.log T|) := by
  subst hd
  -- smoothWickConstant 2 N a mass T = ∫_T^∞ trace(e^{-s M_a})/|Λ| ds
  -- (look up exact unfolding in CovarianceSplit.lean:60).
  -- Use heat_kernel_trace_bound_uniform with d=2:
  --   trace ≤ C · (1 + 1/√s)² · exp(-s·mass²)
  -- |Λ| = N²·a² = L² (using h_vol).
  -- So trace/|Λ| ≤ (C/L²) · (1 + 1/√s)² · exp(-s·mass²)
  --             = (C/L²) · (1 + 2/√s + 1/s) · exp(-s·mass²)
  --             ≤ (C/L²) · (3/s + 1) · exp(-s·mass²)  [for s ≤ 1; need split]
  -- Integrate ∫_T^∞ (3/s + 1) · exp(-s·mass²) ds:
  --   - Split at s = 1: tail is exp-decay (bounded by const).
  --   - Head: ∫_T^1 1/s ds = |log T| (for T ∈ (0, 1]).
  -- Yields A + B·(1 + |log T|) form.
  sorry
```

The integral manipulation is the bulk of Phase 1b. Use Mathlib's
`integral_exp_neg_mul_sq_eq`, `integral_one_div`, `intervalIntegral.integral_add`,
and split at `s = 1`.

---

## Phase 2: rough side, m=1 (≈50 lines)

```lean
-- Easy case: a²·Σ_y C_R(x,y) ≤ T directly.
have m1_case (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a)
    (h_vol : (N : ℝ) * a = L) (T : ℝ) (hT : 0 < T)
    (x : FinLatticeSites 2 N) :
    a^2 * ∑ y : FinLatticeSites 2 N,
      |canonicalRoughCovariance 2 N a mass T x y| ≤ T := by
  -- Constant function = mass²-eigenvector of M_a.
  -- a²·Σ_y (e^{-sM_a})(x, y) = exp(-s·mass²)
  -- a²·Σ_y C_R(x,y) = ∫_0^T exp(-s·mass²) ds = (1−exp(-T·mass²))/mass² ≤ T.
  sorry
```

Need to know how `canonicalRoughCovariance` is defined (FieldDecomposition.lean:1554)
and find/prove the heat-kernel normalization.

---

## Phase 3: rough side, m=2 (Fubini + semigroup; ≈150 lines)

Per Gemini deep-think: the cleanest proof is

```
a²·Σ_y C_R(x,y)² = ∫₀ᵀ ∫₀ᵀ p_{s+t}(x,x) ds dt
                 ≤ ∫₀ᵀ ∫₀ᵀ C(L) / (s+t) ds dt
                 = (2 ln 2) · C(L) · T
```

**Proof skeleton:**

```lean
have m2_case (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a)
    (h_vol : (N : ℝ) * a = L) (T : ℝ) (hT : 0 < T)
    (x : FinLatticeSites 2 N) :
    a^2 * ∑ y, canonicalRoughCovariance 2 N a mass T x y ^ 2 ≤
    (2 * Real.log 2) * C(L) * T := by
  -- Step a: Express C_R(x,y) = ∫₀ᵀ p_s(x,y) ds.  (Schwinger identity.)
  -- Step b: Square and use Fubini:
  --    Σ_y (∫₀ᵀ p_s · ds)·(∫₀ᵀ p_t · dt) = ∫₀ᵀ ∫₀ᵀ Σ_y p_s · p_t · ds dt
  -- Step c: Semigroup property: Σ_y p_s(x,y)·p_t(x,y) = p_{s+t}(x,x)/a²
  --    (in the lattice sum-product form for the matrix product).
  -- Step d: Diagonal bound: a²·p_{s+t}(x,x) = trace(e^{-(s+t)M_a})/|Λ|·1/a²
  --    Wait: p_{s+t}(x,x) is INDEPENDENT of x by translation invariance.
  --    p_s(x,x) = trace(e^{-sM_a})/|Λ|, where |Λ| = N²·a².
  --    So a² · p_{s+t}(x,x) = a² · trace/|Λ| = trace/N².
  --    But trace ≤ C·(1+1/√s)²·N²·exp(-s·mass²), so trace/N² ≤ C·(1+1/√s)²·exp(-s·mass²).
  --    For (s+t) > 0, bound by C(L)/(s+t) · exp(-(s+t)·mass²) ≤ C(L)/(s+t).
  -- Step e: Integrate ∫₀ᵀ ∫₀ᵀ 1/(s+t) ds dt = (2 ln 2) · T.
  sorry
```

The integral `∫₀ᵀ ∫₀ᵀ 1/(s+t) ds dt`: inner = `log((s+T)/s)`, outer:
`∫₀ᵀ (log(2T/T) − log(s+T)/s)...` actually just compute:

```
∫₀ᵀ ∫₀ᵀ 1/(s+t) dt ds = ∫₀ᵀ [log(s+T) − log(s)] ds
                      = [(s+T)·log(s+T) − (s+T) − s·log(s) + s]₀ᵀ
                      = 2T·log(2T) − 2T − T·log(T) + T − (T·log(T) − T)
                      = 2T·log(2T) − 2T·log(T) = 2T·log(2) = (2 log 2) · T.
```

The endpoint `s·log(s)` at `s = 0` requires the limit `lim_{s→0} s·log(s) = 0`,
which is in Mathlib as `Real.tendsto_self_mul_log_nhds_zero_zero`.

---

## Phase 4: rough side, m≥3 (Minkowski; ≈200 lines)

Per Gemini deep-think: Minkowski integral inequality commutes ℓ^m INSIDE
the s-integral.

```
‖C_R(x, ·)‖_{ℓ^m} = ‖∫₀ᵀ p_s(x, ·) ds‖_{ℓ^m}
                 ≤ ∫₀ᵀ ‖p_s(x, ·)‖_{ℓ^m} ds          [Minkowski]
                 ≤ ∫₀ᵀ (C(L)/s)^{1−1/m} ds          [Hölder + diagonal bound]
                 = m · T^{1/m}
```

So `a²·Σ_y C_R^m ≤ C(L)^{m−1} · m^m · T`.

This requires a Minkowski integral inequality for the counting measure on
the lattice (a finite sum) integrated against Lebesgue on `[0, T]`. Mathlib has
`MeasureTheory.Lp.integral_norm_le` and similar — search `Lp.eLpNorm_integral_le`.

Alternative: do it directly without Minkowski for finite sums:

```
(a²·Σ_y C_R(x,y)^m)^{1/m}
  = ‖C_R(x, ·)‖_{ℓ^m_y(a²)}
  = ‖∫₀ᵀ p_s(x, ·) ds‖_{ℓ^m_y(a²)}
  ≤ ∫₀ᵀ ‖p_s(x, ·)‖_{ℓ^m_y(a²)} ds       [Minkowski]
```

For the Minkowski step, in finite-sum form:
```
(Σ_y (∫_0^T f_s(y) ds)^m)^{1/m} ≤ ∫_0^T (Σ_y f_s(y)^m)^{1/m} ds
```
This is the Minkowski integral inequality for the discrete-counting +
Lebesgue product measure. Mathlib lemma to find: search "Minkowski integral"
and "ENNReal Lp norm".

For the inner Hölder step:
```
‖p_s‖_{ℓ^m}^m = a²·Σ_y p_s^m ≤ ‖p_s‖_∞^{m−1} · (a²·Σ_y p_s)
                            = (C/s)^{m−1} · exp(-s·mass²)
                            ≤ (C/s)^{m−1}
```

where `‖p_s‖_∞ = p_s(x, x) = trace/|Λ|/N⁰` ... wait, `p_s(x, x) ≤ C(L)/s`
(diagonal bound, from the upgraded trace bound at d=2 divided by |Λ|/N² = a²,
which is `trace/N²/a² · a² = trace/N² = trace · L²/(N² · L²) = trace/L²·a²·a²/a²...`).

**Codex caveat:** the conventions for `p_s(x, x)` vs `e^{-sM_a}(x, x)` and
the factor of `a²` need careful checking against the existing `latticeGreen`
/ `canonicalRoughCovariance` definitions in
`Pphi2/NelsonEstimate/FieldDecomposition.lean` and `CovarianceSplit.lean`.

---

## Phase 5: assemble the rough-side axiom

Combine the m=1, m=2, m≥3 cases by induction on `m`:

```lean
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
  · omega  -- m = 0 contradicts hm
  · -- m = 1: use Phase 2
    sorry
  · -- m ≥ 2: use Phase 3 (m = 2) or Phase 4 (m ≥ 3) — actually Phase 4 works for all m ≥ 2.
    sorry
```

---

## Acceptance criteria

1. `lake build` clean (no errors, no new sorries beyond what was there at
   commit `27660f0`).
2. The two `axiom` declarations in
   `Pphi2/NelsonEstimate/CovarianceBoundsGJ.lean` are converted to
   `theorem` with full proofs.
3. `#print axioms rough_error_variance` no longer lists either of the two
   Phase B axiom names.
4. `#print axioms torusInteracting_satisfies_OS` (or whichever
   downstream theorem currently lists them transitively) drops two axioms
   from its set.
5. `docs/phase-B-textbook-axioms.md` updated with status "DISCHARGED".
6. `AXIOM_AUDIT.md` and `docs/AXIOM_STATUS.md` updated:
   pphi2 axiom count 19 → 17.
7. `README.md` `## Current status` updated.
8. Commit on `phase-b-discharge` branch, push, update PR #17 (or open new PR).

---

## Existing infrastructure to lean on

- `gaussian_sum_bound` (`HeatKernelBound.lean:204`):
  `Σ_{|k| ≤ M} exp(-α k²) ≤ 1 + √(π/α)`.
- `sin_sq_lower_bound` (`HeatKernelBound.lean:106`): Jordan's inequality.
- `schwinger_smooth`, `schwinger_rough` (`HeatKernelBound.lean:77, 96`):
  Schwinger identities for the covariance-from-heat-kernel integrals.
- `latticeEigenvalue_eq` (`CovarianceSplit.lean` or
  `LatticeMeasure.lean`): the eigenvalue formula.
- `canonicalRoughCovariance` (`FieldDecomposition.lean:1554`).
- `smoothWickConstant`, `roughWickConstant` (`CovarianceSplit.lean:60`,
  near it).
- `roughCovariance_sq_summable` (`CovarianceSplit.lean:203`): finiteness
  result, may inform the structure of Phase 3.

## Helpful Mathlib lemmas

- `Real.sin_pi_sub`, `sin_sq_lower_bound`.
- `Finset.sum_range_reflect`, `Finset.sum_image_le`.
- `Real.tendsto_self_mul_log_nhds_zero_zero` (for `s·log(s) → 0`).
- `Real.exp_le_one_iff`, `Real.exp_pos`, `Real.exp_le_exp`.
- `MeasureTheory.integral_eq_sub_of_hasDerivAt` (for FTC).
- `Real.integrable_exp_neg_mul_sq` (for Gaussian integrability).
- For Minkowski: `MeasureTheory.eLpNorm_integral_le_integral_eLpNorm`
  or `MeasureTheory.Lp.norm_integral_le_integral_norm`.

---

## Estimated remaining effort

| Piece | Lines | Days |
|---|---|---|
| Sorry 1 (`sum_min_le_two_sum`, antitone signature) | ~50 | 0.5 |
| Sorry 2 (`heat_kernel_1d_bound_uniform`, Steps 2-5) | ~150 | 1 |
| Phase 1a (`heat_kernel_trace_bound_uniform`) | ~150 | 1.5 |
| Phase 1b (smooth-side axiom) | ~150 | 1.5 |
| Phase 2 (m=1) | ~50 | 0.5 |
| Phase 3 (m=2) | ~200 | 2 |
| Phase 4 (m≥3) | ~250 | 3 |
| Phase 5 (assembly) | ~100 | 1 |
| Doc updates + verification | — | 0.5 |
| **Total** | **~1100** | **~11.5 active days** |

Calibrated down from the earlier 1–2 wk estimate now that the strategy is
fully verified and Phase 0 helpers are landed. Could be faster with parallel
codex tasks per Phase.

---

## Branch + commit instructions

Work on `phase-b-discharge` (already created). Use sub-commits per phase:
- "Phase 0 sorries filled"
- "Phase 1: smooth-side axiom proved"
- "Phase 2: rough-side m=1"
- "Phase 3: rough-side m=2 via Fubini+semigroup"
- "Phase 4: rough-side m≥3 via Minkowski"
- "Phase 5: assembly + axiom-to-theorem conversion"
- "docs: refresh after Phase B discharge"

Each commit must `lake build` clean. Verify with
`#print axioms` that the axiom set shrinks by 2 once the conversions land.
