# Discharge plan — `degreePiecewiseTail_layerCake_lt_top`

**Target:** convert the staging axiom at
`Pphi2/NelsonEstimate/PolynomialChaosBridge.lean:718` into a proved
theorem. Closes M1 of the T² OS0–OS2 endpoint campaign.

**Branch:** `main` (no feature branch needed; this is a single-axiom
discharge with no API surface changes).

**Estimated effort:** ~150–250 lines / 1–2 days. Direct generalization
of the proved quartic case at `PolynomialChaosBridge.lean:270`.

---

## What needs to land

The axiom is:

```lean
axiom degreePiecewiseTail_layerCake_lt_top
    (P : InteractionPolynomial)
    (K C : ℝ) (hK_pos : 0 < K) (hC_pos : 0 < C) :
    ∫⁻ M in Set.Ioi (0 : ℝ),
      degreePiecewiseTail P K C M *
        ENNReal.ofReal (2 * Real.exp (2 * M)) < ⊤
```

Pure Lebesgue integrability — finiteness of a Lebesgue integral whose
integrand has doubly-exponential decay (in M) for large M. The only
"hard" part is the algebraic generalization of the quartic case's
exponent bookkeeping from `^(1/2)` (sqrt) to `^(1/k)` where
`k := degreeCutoffPower P = P.n / 2`.

---

## Reference: the proved quartic case

`PolynomialChaosBridge.lean:270` — `quarticPiecewiseTail_layerCake_lt_top`,
~200 lines. Three-step structure:

1. **Pick threshold `T₀`** (line 274–280) — uses
   `quarticDecayConstant` + `quartic_exp_growth_threshold` to find a
   point past which the cutoff tail decays fast enough to dominate
   `exp(2M)`.
2. **Apply** `Pphi2.IntegrabilityHelpers.lintegral_layer_cake_lt_top_of_eventual_decay`
   (line 281–282) — the generic helper splits the integral into a
   small-M piece and a large-M piece.
3. **Small-M piece** (line 283–318): bound `quarticPiecewiseTail ≤ 2`
   on `(0, T₀]`, integrand bounded by `4 · exp(2·T₀)` on a bounded
   interval, integral finite.
4. **Large-M piece** (line 319–end): bound `quarticCutoffTail` by an
   explicit `exp(-A · exp(s/4))` decay envelope where
   `s = sqrt(M/(2C))`, then chain to `exp(2M)` via
   `quartic_exp_growth_threshold`.

---

## The 1-to-1 generalization mapping

| Quartic | General `P` (with `k := degreeCutoffPower P = P.n / 2`) |
|---|---|
| `Real.sqrt (M / (2*C))` | `(M / (2*C)) ^ (1 / (k : ℝ))` |
| `s ^ (2 : ℝ)` (= `M / (2C)`) | `s ^ (k : ℝ)` (= `M / (2C)`, where `s := (M/(2C))^(1/k)`) |
| `s ^ 3` (= `(1 + |log T|) ^ 3` since `P.n - 1 = 3`) | `s ^ (P.n - 1 : ℕ)` |
| `Real.sqrt (...)` (denominator of chaos arg) | `(...)  ^ (1 / k)` |
| `chaosTailConstant 4` | `chaosTailConstant P.n` |
| `quarticDecayConstant K C` | new `degreeDecayConstant P K C` (define analogously) |
| `quartic_exp_growth_threshold` (real-analysis helper) | new `degree_exp_growth_threshold` (analogous) |
| `sqrt_exp_sub` (algebraic identity `sqrt(exp(1-s)) = exp((1-s)/2)`) | new `rpow_inv_exp_sub` (analogous: `(exp(1-s)) ^ (1/(2k)) = exp((1-s)/(2k))`) |

---

## Required new helpers (add to `PolynomialChaosBridge.lean`)

### 1. `degreeDecayConstant`

```lean
private def degreeDecayConstant
    (P : InteractionPolynomial) (K C : ℝ) : ℝ :=
  Pphi2.ChaosTailBridge.chaosTailConstant P.n *
    Real.sqrt (C / (2 * Real.sqrt K * Real.exp (1 / 2)))
```

Wait — the quartic version uses `sqrt` for the final wrapping. For
general `P`, this should be `^(1/(2k))` or similar. Look at how the
quartic constant is constructed by chaining:

```
chaosTailConstant 4 *
  Real.sqrt ((M/2) / (denominator))
= chaosTailConstant 4 *
  Real.sqrt ((M/2) / (2 * sqrt (...)))
≥ chaosTailConstant 4 *
  Real.sqrt (C / (2 * sqrt K * exp((1-s)/2))) * exp(s/4)
= quarticDecayConstant K C * exp(s/4)
```

The general-`P` analogue: the chaos exponent is `1/k` instead of `1/2`,
so the bound becomes
```
chaosTailConstant P.n *
  ((M/2) / (denominator)) ^ (1/k)
```
and the factoring out gives
`degreeDecayConstant P K C * exp(s / (2k))`
where `s := (M/(2C))^(1/k)`.

Define:
```lean
private def degreeDecayConstant
    (P : InteractionPolynomial) (K C : ℝ) : ℝ :=
  Pphi2.ChaosTailBridge.chaosTailConstant P.n *
    (C / (2 * (K * Real.exp 1) ^ (1 / (2 * (degreeCutoffPower P : ℝ))))) ^
      (1 / (degreeCutoffPower P : ℝ))
```

(Exact form to tune during the proof to match what the chaining produces.)

### 2. `degree_exp_growth_threshold`

```lean
private lemma degree_exp_growth_threshold
    (P : InteractionPolynomial) {A B : ℝ} (hA : 0 < A) :
    ∃ S : ℝ, 1 ≤ S ∧
      ∀ s : ℝ, S ≤ s →
        A * Real.exp (s / (2 * (degreeCutoffPower P : ℝ))) ≥ 2 * s ^ (degreeCutoffPower P : ℝ) + B
```

(Replace the quartic case's `exp(s/4)` denominator-4 with
`exp(s/(2k))` and the `s^2` with `s^k`. Proof: same — for sufficiently
large `s`, the exponential dominates any polynomial in `s`.)

The quartic version is at `PolynomialChaosBridge.lean:238`. Generalize
by replacing `4` with `2k` and `s^2` with `s^k`.

### 3. `rpow_inv_exp_sub`

```lean
private lemma rpow_inv_exp_sub
    (P : InteractionPolynomial) (s : ℝ) :
    (Real.exp (1 - s)) ^ (1 / (2 * (degreeCutoffPower P : ℝ))) =
      Real.exp ((1 - s) / (2 * (degreeCutoffPower P : ℝ))) := by
  rw [← Real.exp_one_rpow, ← Real.exp_mul]; congr 1; ring
```

Analogue of `sqrt_exp_sub` (which uses the special case `2k = 2`).

---

## The actual proof skeleton

```lean
theorem degreePiecewiseTail_layerCake_lt_top
    (P : InteractionPolynomial)
    (K C : ℝ) (hK_pos : 0 < K) (hC_pos : 0 < C) :
    ∫⁻ M in Set.Ioi (0 : ℝ),
      degreePiecewiseTail P K C M *
        ENNReal.ofReal (2 * Real.exp (2 * M)) < ⊤ := by
  let k : ℕ := Pphi2.DynamicalCutoff.degreeCutoffPower P
  have hk_pos : 0 < k := Pphi2.DynamicalCutoff.degreeCutoffPower_pos P
  let A := degreeDecayConstant P K C
  have hA_pos : 0 < A := degreeDecayConstant_pos P hK_pos hC_pos
  obtain ⟨S, hS_ge_one, hS_growth⟩ :=
    degree_exp_growth_threshold P (A := A)
      (B := some_bound_involving_C_and_k) hA_pos
  let T₀ : ℝ := 2 * C * S ^ (k : ℝ)
  have hT₀_pos : 0 < T₀ := by positivity
  refine Pphi2.IntegrabilityHelpers.lintegral_layer_cake_lt_top_of_eventual_decay
    (ψ := degreePiecewiseTail P K C) T₀ hT₀_pos ?_ ?_
  · -- Small-M piece: same as quartic. Bound by constant `4 · exp(2·T₀)`.
    -- Use `degreePiecewiseTail_le_two` (already defined at line 706).
    -- ... (~30 lines, identical structure to quartic small-M block)
    sorry
  · -- Large-M piece: bound the cutoff tail by an explicit decay envelope.
    intro M hM
    -- 1. Show `2 * C < M` (from M > T₀ ≥ 2C·S^k ≥ 2C since S ≥ 1).
    -- 2. Define `s := (M/(2C))^(1/k)`; note `s^k = M/(2C)` and `s ≥ S`.
    -- 3. Use degreeDynamicalCutoffScale_eq_exp to rewrite the cutoff.
    -- 4. Chain through chaos tail constant + denominator bound.
    -- 5. Use degree_exp_growth_threshold to dominate `exp(2M)`.
    -- ... (~120 lines, mirrors quartic large-M block with `s^(1/2)` → `s^(1/k)`)
    sorry
```

---

## Mathlib helpers used (already in scope from quartic case)

- `Real.exp_le_one_iff`, `Real.exp_pos`, `Real.exp_le_exp`, `Real.exp_add`,
  `Real.exp_mul`, `Real.exp_zero`, `Real.exp_one_rpow`
- `Real.rpow_natCast`, `Real.rpow_one`, `Real.rpow_mul`, `Real.rpow_le_rpow`,
  `Real.rpow_nonneg`
- `MeasureTheory.setLIntegral_mono'`, `MeasureTheory.setLIntegral_const`,
  `measure_Ioc_lt_top`
- `ENNReal.ofReal_le_ofReal`, `ENNReal.ofReal_lt_top`,
  `ENNReal.ofReal_mul`, `ENNReal.mul_lt_top`
- `Real.sqrt` → replace with `· ^ (1 / (2 * (k:ℝ)))` throughout

---

## Acceptance criteria

1. `lake build Pphi2.NelsonEstimate.PolynomialChaosBridge` clean.
2. `lake build` full project clean.
3. `axiom degreePiecewiseTail_layerCake_lt_top` removed; replaced by a
   `theorem` of the same signature.
4. `#print axioms Pphi2.torusInteracting_satisfies_OS` no longer cites
   `Pphi2.degreePiecewiseTail_layerCake_lt_top`. Closure becomes:
   ```
   [propext, Classical.choice, Quot.sound,
    gross_lsi_implies_hypercontractive,
    GaussianFin.ouSemigroupFin_entropy_sq_decay_bound,
    GaussianFin.ouSemigroupFin_l2_sq_hasDerivWithinAt,
    GaussianFin.ouSemigroupFin_preserves_IsCore]
   ```
   This is **M1 in `docs/T2-master-plan.md`** — fully clean.
5. Pphi2 active axiom count: 18 → 17 (one staging axiom retired; the
   `nelson_exponential_estimate_master_bounded` compatibility axiom
   stays, off T² critical path).
6. Update `docs/T2-master-plan.md` to mark the workstream B follow-up
   as ✅ DISCHARGED and Update the M1 milestone status.
7. Commit message format: `Workstream B follow-up: degreePiecewiseTail_layerCake_lt_top discharged`.

---

## Why this is well-scoped

- **No new mathematical content.** Pure Lebesgue integrability —
  doubly-exp tail dominates `exp(2M)`. The general `P` case has the
  *same* tail shape as the quartic case, just with a different exponent
  (1/k instead of 1/2) on the inner `M` factor.
- **The framework is already in place.** The generic integrability
  helper `lintegral_layer_cake_lt_top_of_eventual_decay` doesn't care
  about the specific functional form. All the infrastructure
  (`degreeDynamicalCutoffScale`, `degreeCutoffPower`, `degreeCutoffTail`,
  `degreePiecewiseTail`) is already defined.
- **Risk is low.** The quartic version was successfully discharged at
  commit `59c771f`; the proof template + Mathlib helpers used there
  are well-understood. The main pitfall is sign/exponent juggling with
  `Real.rpow (1/k)` instead of `Real.sqrt` — careful but mechanical.

---

## After this lands

Master plan's M1 milestone is fully reached. The T² OS0–OS2 endpoint's
axiom closure becomes exactly the 4 inherited markov-semigroups
textbook axioms (Gross + 3 GaussianFin BE tensor-lifts) — the
"defensible mathematical resting point" mentioned in the master plan.

Further axiom reductions then proceed via Phase 2.5 / N1.b / N1.c /
Route A / G2.a / G2.b per the master plan inventory.
