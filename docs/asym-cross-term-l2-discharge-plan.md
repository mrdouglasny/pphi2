# Asym cross-term L² bound — discharge plan for the remaining UNIT-5 sorry

> **STATUS 2026-05-29: ✅ DISCHARGED.** `asymCanonicalCrossTerm_l2_sq_le` is now a
> THEOREM (`Pphi2/NelsonEstimate/AsymCrossTermL2Identity.lean`, commit `6136a92`)
> with `#axioms = [propext, Classical.choice, Quot.sound]`. Branch state is
> **21 raw / 19 real axioms, 0 sorries**. The discharge followed the §1–§8
> staged plan below; the final scope was ~1845 lines in
> `AsymCrossTermL2Identity.lean` (§1 manually seeded + §2–§4 + §5–§8 in two
> focused Codex passes on the public `wickPower_two_site_pi_gaussianReal_*`
> helpers). The plan below is kept for historical reference.

*2026-05-28. Plan for proving `asymCanonicalCrossTerm_l2_sq_le`
(`Pphi2/NelsonEstimate/AsymRoughErrorVariance.lean:144`), the only remaining
documented sorry on the `cylinder-isotropic-lattice` branch (21 raw / 19 real
axioms / 1 sorry). The downstream `asymRoughError_variance` (line 162) is
already proved on top of it.*

## What's needed

The sorry's statement is the per-cross-term L² bound:

```lean
∃ K > 0, ∀ (Nt Ns a Lt Ls T η), …,
  ∫ η, (asymCanonicalCrossTerm Nt Ns a mass T η k j) ^ 2
    ∂(asymCanonicalJointMeasure Nt Ns) ≤
  K * T * (1 + |Real.log T|) ^ j
```

The square version `canonicalCrossTerm_l2_sq_le`
(`RoughErrorBound.lean:3050–3290`) discharges this in ~210 lines of calc,
but it consumes several deeper analytical inputs whose asym analogues do
not yet exist:

| Square input | Status (square) | Asym analog |
|---|---|---|
| `smoothWickConstant_le_log_uniform_in_aN` | proved | `asymSmoothWickConstant_le_log_uniform` ✅ proved (`48b479e`) |
| `canonicalRoughCovariance_pow_sum_le_uniform_in_aN` (unified ∀ m ≥ 1) | proved | needs case-split assembly from `_pow_{one,two}_sum_le_uniform` (`014c598`) + `_of_three_le` (`b50014e`) |
| `abs_canonicalSmoothCovariance_le_smoothWickConstant` (`FieldDecomposition.lean:3812`) | proved | needs port (+ `asymCanonicalSmoothCovariance` def) |
| `canonicalCrossTerm_l2_sq_eq_covSum` (`RoughErrorBound.lean:2855`, ~195 lines) | proved | needs port (the **deep input**: ∫(CrossTerm)² = (a²)²·j!·(k−j)!·Σ_{x,y} C_S^j·C_R^(k−j)) |

The 4th row is the genuine analytical heart. It rests on six
`canonical{Smooth,Rough}WickPower_two_site_marginal_{integrable,eq_zero_of_ne,eq_diag}`
lemmas (`FieldDecomposition.lean:3400–3805`, ~6×70 lines), which in turn
rest on three index-polymorphic helpers
`wickPower_two_site_pi_gaussianReal_{integrable,eq_zero_of_ne,eq_diag}` —
**these are fully generic over the mode index** and were just made public
(`FieldDecomposition.lean:2997 / 3106 / 3236`, this session) so the asym
port can call them directly.

## Concrete port scope (best estimate)

| Stage | Lines | Notes |
|---|---|---|
| 0 | (done) | Make 3 generic `wickPower_two_site_pi_gaussianReal_*` helpers public. |
| 1 | ~60 | `asymCanonical{Smooth,Rough}Gamma` defs + `…FieldFunctionOf{Fst,Snd}_eq_sum_gamma`. Mechanical. |
| 2 | ~120 | `asymCanonical{Smooth,Rough}Gamma_sq_sum_eq_…WickConstant`. Site-variance identity; mirrors the proved `wickConstantAsym_eq_variance` for the SMOOTH covariance separately. |
| 3 | ~80 | `asymCanonical{Smooth,Rough}Gamma_dot_product_eq_…Covariance`. New defs for `asymCanonicalSmoothCovariance` / `asymCanonicalRoughCovariance` (the latter already exists) + the `Σ_m γ_x·γ_y = C(x,y)` identity. |
| 4 | ~420 | 6 `asymCanonical{Smooth,Rough}WickPower_two_site_marginal_{integrable,eq_zero_of_ne,eq_diag}` lemmas, each ~70 lines via the now-public generic helpers + stages 1–3. |
| 5 | ~200 | `asymCanonicalCrossTerm_l2_sq_eq_covSum` — the central identity. |
| 6 | ~30 | `abs_asymCanonicalSmoothCovariance_le_asymSmoothWickConstant`. |
| 7 | ~30 | Unified `asymCanonicalRoughCovariance_pow_sum_le_uniform` (case-split on m=1, 2, ≥3). |
| 8 | ~150 | Discharge `asymCanonicalCrossTerm_l2_sq_le`, mirroring the square calc at `RoughErrorBound.lean:3050–3263`. |
| **Total** | **≈ 1090** | |

This is comparable to the **whole UNIT 5 port that landed in `e33cef7`** (659
lines) — i.e. another ~1100 lines of careful, mechanical translation.

## Alternative — single textbook axiom (~30 min of work)

Instead of porting stages 4–5 (which together are ~620 of the 1090 lines),
introduce one vetted textbook axiom capturing the Wick L² inner-product
identity — exactly the conclusion of stage 5:

```lean
/-- Wick L² inner-product identity for the heterogeneous-lattice joint
Gaussian. Heterogeneous analogue of the proved square
`canonicalCrossTerm_l2_sq_eq_covSum`; textbook fact (Janson, *Gaussian
Hilbert Spaces*, Ch. 3; Glimm-Jaffe Ch. 9; Simon §I.6). -/
axiom asymCanonicalCrossTerm_l2_sq_eq_covSum
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (hT : 0 < T) (k j : ℕ) :
    ∫ η, (asymCanonicalCrossTerm Nt Ns a mass T η k j) ^ 2
        ∂(asymCanonicalJointMeasure Nt Ns) =
      ((a ^ 2) * (a ^ 2)) * ((j.factorial : ℝ) * ((k - j).factorial : ℝ)) *
        ∑ x : AsymLatticeSites Nt Ns,
          ∑ y : AsymLatticeSites Nt Ns,
            asymCanonicalSmoothCovariance Nt Ns a mass T x y ^ j *
              asymCanonicalRoughCovariance Nt Ns a mass T x y ^ (k - j)
```

Then stages 1, 3, 6, 7, 8 (the algebraic / structural parts, ~340 lines)
suffice to close the sorry — replacing the sorry with one vetted axiom.

Trade-off:

* **Full port (~1090 lines, ~hours)**: discharges the sorry to a theorem;
  `#axioms` stays `[propext, Classical.choice, Quot.sound]`. Pure win on
  audit count.
* **Axiom route (~340 lines, ~30 min)**: closes the sorry but adds one
  vetted textbook axiom. Net: 21 raw / 19 real axioms / 0 sorries → 22
  raw / 20 real axioms / 0 sorries. The axiom is exactly the conclusion
  of a proved square theorem (so it's known-correct, just deferred).

## Recommendation

If the goal is to **maximize the proof-graph reduction** of `asymChaosCutoffDecomposition`
(downstream UNITs 6 + 7), the **axiom route** gets to a sorry-free branch
quickly, and the deferred port is well-isolated for later attack.

If the goal is to **eliminate the only sorry on the branch**, the **full
port** is the right move; it's bounded (~1090 lines), every input either
exists or has a clear template, and the work is mechanical translation.
