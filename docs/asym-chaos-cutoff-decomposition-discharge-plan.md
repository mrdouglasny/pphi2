# `asymChaosCutoffDecomposition` discharge plan (UNITs 6 + 7) — ✅ DONE 2026-05-31

*2026-05-29. Plan for promoting `asymChaosCutoffDecomposition`
(`Pphi2/AsymTorus/AsymNelson.lean:62`) from a deep-think-vetted axiom to a
theorem. After this discharge, the branch goes to **20 raw / 18 real axioms,
0 sorries** (was 21/19/0) and `asymNelson_exponential_estimate_iso`
becomes axiom-free modulo Mathlib's standard trio.*

**Update 2026-05-31**: DONE. UNIT 7 landed in commit `c5d91e7`. Counts:
pphi2 21/0 → **20/0** (19 real → **18 real**). The trivial-split proof
(V_S = -(M/2), E_R = V_a + M/2) came in at ~100 lines — much shorter than
the 150-250 originally estimated — because the V_S/E_R "joint-split" can
be avoided entirely (the pushforward + naturality do the work at the
measure level, not pointwise on Configuration).

## Target — exact axiom

```lean
axiom asymChaosCutoffDecomposition
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Lt Ls : ℝ) (hLt : 0 < Lt) (hLs : 0 < Ls) :
    ∃ ψ : ℝ → ENNReal,
      (∫⁻ M in Set.Ioi (0 : ℝ), ψ M * ENNReal.ofReal (2 * Real.exp (2 * M)) < ⊤) ∧
      ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
        (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls →
        ∃ V_S E_R : ℝ → Configuration (AsymLatticeField Nt Ns) → ℝ,
          (∀ M ω, interactionFunctionalAsym Nt Ns P a mass ω = V_S M ω + E_R M ω) ∧
          (∀ M ω, -(M / 2) ≤ V_S M ω) ∧
          (∀ M, 0 < M →
            (latticeGaussianMeasureAsym Nt Ns a mass ha hmass)
              {ω | E_R M ω ≤ -(M / 2)} ≤ ψ M)
```

I.e. **construct** witnesses `(ψ, V_S, E_R)` and prove the four conditions.

## The four conditions, and what discharges each

| # | Condition | Discharged by |
|---|---|---|
| **C1** | `interactionFunctionalAsym = V_S(M) + E_R(M)` (the decomposition) | the pointwise lemma `asymCanonicalRoughError_pointwise_decomposition` + the asym `interactionFunctionalAsym ↔ asymCanonicalFullInteractionJoint` identity (under the joint-measure pullback) |
| **C2** | `-(M/2) ≤ V_S(M, ω)` (the smooth lower bound at the cutoff scale) | `asymCanonicalSmoothInteraction_lower_bound_at_cutoff_uniform` (UNIT 2, proved `1495eb6`) |
| **C3** | `μ_GFF { E_R(M) ≤ -(M/2) } ≤ ψ(M)` (the rough-tail bound) | **UNIT 6** — port of square `canonicalRoughError_neg_tail_uniform_in_aN` (`Pphi2/NelsonEstimate/RoughErrorBound.lean:3799`) via the proved generic engine `Pphi2.ChaosTailBridge.chaos_neg_tail_bound_explicit` (`ChaosTailBridge.lean:438`), consuming `asymRoughError_variance` (UNIT 5, proved `6136a92`) |
| **C4** | `∫⁻ ψ · 2 e^{2M} < ⊤` (the integrability) | falls out of the chosen `ψ` (typically `ψ(M) = chaosTailConstant_d · M^{-d}` or a super-exponential bound), proved via `ENNReal.lintegral_mul_const` + standard integrability lemmas |

So **only C3 is genuinely new analytical content (UNIT 6)**; C1, C2, C4 are wiring on top of proved theorems.

## The bridge subtlety — joint vs config

The axiom is stated over `ω : Configuration (AsymLatticeField Nt Ns)` (the
lattice GFF sample space), but the proved infrastructure
(`asymCanonicalSmoothInteraction`, `asymCanonicalRoughError`,
`asymRoughError_variance`) is on `η : AsymCanonicalJoint Nt Ns`. These two
sides are bridged by

```lean
asymCanonicalJointMeasure_map_sumConfig :
    (asymCanonicalJointMeasure Nt Ns).map (asymCanonicalSumConfig …) =
      latticeGaussianMeasureAsym Nt Ns a mass ha hmass
```

(proved in `AsymFieldDecomposition.lean`, commit `ab6dcdb`).

**Implementation choice for `V_S`, `E_R`:** define them as joint-side
functions composed with the inverse of the sum-config map *or*, more
robustly, take the joint-side `V_S, E_R` and **lift to `Configuration`** via
the joint-decomposition split `ω ↦ (φ_S(ω), φ_R(ω))`. The latter is the
cleaner formulation: any lattice field `ω : AsymLatticeField Nt Ns →
Configuration ...` admits the smooth/rough decomposition through DFT
inversion, and the smooth piece evaluates the smooth Wick polynomial.

Concretely: define

```lean
V_S M ω := asymCanonicalSmoothInteraction Nt Ns a mass
  (degreeDynamicalCutoffScale P C M) P (asymJointSplitOf ω)
E_R M ω := interactionFunctionalAsym Nt Ns P a mass ω − V_S M ω
```

where `asymJointSplitOf : Configuration (AsymLatticeField Nt Ns) →
AsymCanonicalJoint Nt Ns` extracts the smooth/rough Gaussian-coordinate
representation (via the pushforward inverse — measure-equivalent, not
literal inverse). C1 then follows definitionally; the smooth lower bound
C2 uses UNIT 2 directly; C3 uses UNIT 6 (the rough-tail bound, which is
itself stated over the joint measure and transferred via the pushforward).

## UNIT 6 — rough-tail bound

### Scoping correction (2026-05-30)

The original plan assumed the asym side already had the chaos-membership
stack analogous to the square's. **It does not.** A scan against
`Pphi2/NelsonEstimate/RoughErrorBound.lean` (the square's reference
template) found that only the L² variance bound (UNIT 5) is present;
none of the `std`-pulled-back representatives, none of their
chaos-`P.n` membership lemmas, and none of the
`stdGaussianFin nStd`-shaped pushforward exist on the asym side. The
existing `asymCanonicalJointMeasure_map_stdGaussianEuclidean`
(`AsymFieldDecomposition.lean:133`) lands on
`EuclideanSpace ℝ (AsymCanonicalJointSumIndex Nt Ns)`, not on
`Fin nStd → ℝ`, which is what `chaos_neg_tail_bound_explicit` consumes.

The plan-asset gap, by row:

| Asset | Square (template) | Asym |
|---|---|---|
| Joint↔`Fin nStd → ℝ` measurable equiv | `canonicalJointStdGaussianMeasurableEquiv` (`FieldDecomposition.lean:72`) | **missing** |
| Pushforward to `stdGaussianFin nStd` | `canonicalJointMeasure_map_stdGaussian` (`FieldDecomposition.lean:96`) | **missing** |
| `…CrossTermStd` + `…CrossTermStd_eq` | `RoughErrorBound.lean:1628`, `:1635` | **missing** |
| `…CrossTermStd_mem_wienerChaosLE` | `RoughErrorBound.lean:1640` (112 lines) | **missing** |
| `…CrossTermLinearCombo_mem_wienerChaosLE` | `RoughErrorBound.lean:1752` (100 lines) | **missing** |
| `…RoughErrorStd` + `_eq` + `_mem_wienerChaosLE` | `RoughErrorBound.lean:1854`, `:1863`, `:1876` (154 lines) | **missing** |
| `_uniform_in_aN` wrapper | `RoughErrorBound.lean:3799` (127 lines) | **= UNIT 6 target** |
| L² variance bound | (square) `rough_error_variance` | ✅ UNIT 5 `asymRoughError_variance` |

The chaos-side proofs are dimension-symmetric — they only care about the
size of the index set (`Fintype.card (AsymCanonicalJointSumIndex Nt Ns)`)
and the existence of the Wick/Hermite decomposition, not about whether
the lattice is `N × N` or `Nt × Ns`. Port is therefore mostly mechanical
search-and-replace from the square stack, but the **volume** is what
makes UNIT 6 a multi-day port rather than a wiring exercise.

### Target wrapper (UNIT 6b)

```lean
theorem asymCanonicalRoughError_neg_tail_uniform
    (P : InteractionPolynomial)
    (mass Lt Ls : ℝ) (hLt : 0 < Lt) (hLs : 0 < Ls) (hmass : 0 < mass) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (_ha : 0 < a)
        (_hvolt : (Nt : ℝ) * a = Lt) (_hvols : (Ns : ℝ) * a = Ls)
        (T : ℝ) (_hT : 0 < T)
        (t : ℝ) (_ht : 0 < t),
        (asymCanonicalJointMeasure Nt Ns)
          {η | asymCanonicalRoughError Nt Ns a mass T P η ≤ -t} ≤
            2 * ENNReal.ofReal
              (Real.exp
                (-(Pphi2.ChaosTailBridge.chaosTailConstant P.n) *
                  (t /
                    (2 * Real.sqrt
                      (K * T * (1 + |Real.log T|) ^ (P.n - 1)))) ^
                    ((2 : ℝ) / P.n)))
```

Body method (mirror `canonicalRoughError_neg_tail_uniform_in_aN`):
extract `K` from `asymRoughError_variance` (UNIT 5); build
`F : Lp ℝ 2 (stdGaussianFin nStd)` from `asymCanonicalRoughErrorStd`
via the missing pushforward; transfer the L² bound to a norm bound on
`F`; close with `chaos_neg_tail_bound_explicit`.

### UNIT 6a — chaos-membership infrastructure (~400 lines)

Mechanical port from the square's `RoughErrorBound.lean` lines
**1620 – 2006** (and `FieldDecomposition.lean` lines **72 – 130**),
specialized to `AsymCanonicalJoint Nt Ns` and
`AsymCanonicalJointSumIndex Nt Ns`. Outputs:

* `asymCanonicalJointStdGaussianMeasurableEquiv`
* `asymCanonicalJointMeasure_map_stdGaussian`
* `asymCanonicalCrossTermStd` + `asymCanonicalCrossTermStd_eq`
* `asymCanonicalCrossTermStd_mem_wienerChaosLE`
* `asymCanonicalCrossTermLinearCombo_mem_wienerChaosLE`
* `asymCanonicalRoughErrorStd` + `asymCanonicalRoughErrorStd_eq`
* `asymCanonicalRoughErrorStd_mem_wienerChaosLE`

### UNIT 6b — the wrapper (~120 lines)

Mirror of square `RoughErrorBound.lean:3799–3919`, with `2 N` → `Nt Ns`
and the (single) variance hypothesis switched to UNIT 5.

**Revised UNIT 6 total: ~500–600 lines** (was ~80–150). Still smaller
than the cross-term L² port (1845 lines); execution risk is low because
the square is a line-by-line template.

## UNIT 7 — axiom discharge assembly

Combines UNITs 2 + 5 + 6 into the existential package. Skeleton:

```lean
theorem asymChaosCutoffDecomposition_proof
    (P) (mass : ℝ) (hmass : 0 < mass)
    (Lt Ls : ℝ) (hLt : 0 < Lt) (hLs : 0 < Ls) :
    [the axiom's existential statement] := by
  obtain ⟨C, hC_pos, hC_smooth⟩ :=
    asymCanonicalSmoothInteraction_lower_bound_at_cutoff_uniform P mass Lt Ls hLt hLs hmass
  obtain ⟨K_tail, hK_pos, hK_tail⟩ :=
    asymCanonicalRoughError_neg_tail_uniform P mass Lt Ls hLt hLs hmass
  refine ⟨fun M => ENNReal.ofReal (K_tail · …), ?_int, ?_setup⟩
  · -- C4: ∫⁻ ψ · 2 e^{2M} < ⊤
    …
  · intro Nt Ns hNt hNs a ha hvolt hvols
    refine ⟨V_S, E_R, ?_C1, ?_C2, ?_C3⟩
    · -- C1: V_a = V_S(M) + E_R(M) — definitional after the joint-decomposition split
      intro M ω
      simp [V_S, E_R]
    · -- C2: -(M/2) ≤ V_S(M)
      intro M ω
      exact hC_smooth Nt Ns a ha hvolt hvols M (by linarith [hM_ge_2C]) (asymJointSplitOf ω)
    · -- C3: μ_GFF { E_R(M) ≤ -(M/2) } ≤ ψ(M)
      intro M hM
      …  -- pushforward bridge + UNIT 6
```

Estimated scope: **~150–250 lines** (the joint-split + pushforward bridge
is the longer part; the existential assembly itself is short).

## Total estimate (revised 2026-05-30)

* UNIT 6a (chaos-membership infrastructure port from square): ~400 lines
* UNIT 6b (`asymCanonicalRoughError_neg_tail_uniform` wrapper): ~120 lines
* UNIT 7 (axiom-discharge existential assembly): ~150–250 lines
* Joint-split helper `asymJointSplitOf` + pushforward-bridge lemmas: ~60–100 lines

**Revised total: ~700–900 lines.** Larger than the original ~290–500
estimate because UNIT 6 has to port the entire chaos-membership stack
from the square (not just wire a generic engine). Still meaningfully
smaller than the cross-term L² port (~1845 lines), and execution risk
is low — the square's `RoughErrorBound.lean` is a line-by-line
template, so most of UNIT 6 is mechanical search-and-replace.

## Recommended strategy (revised 2026-05-31)

Same playbook that worked for the cross-term L² discharge, with the
UNIT 6 step split into the mechanical port (6a) and the wrapper (6b):

1. ✅ DONE — recon `chaos_neg_tail_bound_explicit` + the square's
   `canonicalRoughError_neg_tail_uniform_in_aN` and chaos-membership
   stack; identified the missing asym infrastructure (see Asset gap
   table above).
2. ✅ DONE (commit `32f9484`) — UNIT 6a mechanical port of the square's
   chaos-membership stack (`RoughErrorBound.lean:1620–2006` and
   `FieldDecomposition.lean:72–130`) to the asym namespace, in
   `Pphi2/NelsonEstimate/AsymRoughErrorChaosStd.lean` (786 lines, all
   10 deliverables). The asym gamma stack was reused from
   `AsymCrossTermL2Identity.lean` (UNIT 5 territory).
3. ✅ DONE — UNIT 6b wrapper. Added two theorems to
   `AsymRoughErrorChaosStd.lean`:
   * `asymCanonicalRoughError_neg_tail_of_stdGaussian_explicit_ae`
     (line 791): generic helper that transfers a chaos-tail bound on a
     standard-Gaussian `Lp` representative back to the joint measure.
   * `asymCanonicalRoughError_neg_tail_uniform` (line 871): packages
     UNIT 5 (variance) + UNIT 6a (chaos membership) + the generic
     helper into the dimension-independent polynomial-chaos
     concentration bound.
4. Decide whether `asymJointSplitOf` needs to be constructive (likely
   yes, via the `evalMap`/`evalMapInv` already proved in
   `AsymFieldDecomposition.lean`) or can be measure-theoretic only.
5. Launch focused pass on UNIT 7 + the joint-split. Commit, verify.
6. Update counts (21/19 → 20/18) and AXIOM_AUDIT.

After this discharge, the only project-introduced axiom on the branch
toward cylinder OS0/OS1/OS2/OS3 is
`asymInteracting_expMoment_volume_uniform` (the §4 cylinder
transfer-matrix-gap input — the genuine deep one).
