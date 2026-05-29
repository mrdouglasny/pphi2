# `asymChaosCutoffDecomposition` discharge plan (UNITs 6 + 7)

*2026-05-29. Plan for promoting `asymChaosCutoffDecomposition`
(`Pphi2/AsymTorus/AsymNelson.lean:62`) from a deep-think-vetted axiom to a
theorem. After this discharge, the branch goes to **20 raw / 18 real axioms,
0 sorries** (was 21/19/0) and `asymNelson_exponential_estimate_iso`
becomes axiom-free modulo Mathlib's standard trio.*

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

Target:

```lean
theorem asymCanonicalRoughError_neg_tail_uniform
    (P) (mass Lt Ls : ℝ) (hLt hLs hmass) :
    ∃ K_tail, ∀ Nt Ns a (ha) (hvolt hvols),
      ∀ M > 0,
        (asymCanonicalJointMeasure Nt Ns)
          { η | asymCanonicalRoughError Nt Ns a mass (T(M)) P η ≤ -(M/2) } ≤
        ENNReal.ofReal (K_tail · M^{- (P.n / 2)})
```

(or whatever shape `chaos_neg_tail_bound_explicit` produces — read the
square at `RoughErrorBound.lean:3799` for the exact constant form). Method:
the generic `chaos_neg_tail_bound_explicit` (proved in
`ChaosTailBridge.lean:438`) takes an L²-bound on a chaos-`d` element and
returns a polynomial-power tail; `asymRoughError_variance` (UNIT 5)
provides the L² bound, with `d = P.n` (the chaos degree of the rough
error).

Estimated scope: **~80–150 lines**. The generic engine does all the work;
this is wrapping it with the asym names. Square has 4 versions
(`of_stdGaussian`, `of_stdGaussian_explicit`,
`of_stdGaussian_explicit_ae`, `uniform_in_aN`) at `RoughErrorBound.lean`
:580, :650, :723, :3799 — the asym port mirrors the `_uniform_in_aN`
shape.

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

## Total estimate

* UNIT 6: ~80–150 lines
* UNIT 7: ~150–250 lines
* Joint-split helper `asymJointSplitOf` + pushforward-bridge lemmas: ~60–100 lines

**Total: ~290–500 lines.** Smaller than the cross-term L² port (~1845 lines) and
*much* more wiring-oriented — the analytical content is already proved (UNITs 2, 5;
generic `chaos_neg_tail_bound_explicit`; pushforward identity).

## Recommended strategy

Same playbook that worked for the cross-term L² discharge:

1. Quickly check `chaos_neg_tail_bound_explicit`'s exact signature + the
   square's `canonicalRoughError_neg_tail_uniform_in_aN` proof pattern.
2. Decide whether `asymJointSplitOf` needs to be constructive (likely
   yes, via the `evalMap`/`evalMapInv` already proved in
   `AsymFieldDecomposition.lean`) or can be measure-theoretic only.
3. Launch one focused Codex pass on UNIT 6 (the wiring), commit, verify.
4. Launch a second focused pass on UNIT 7 + the joint-split, commit, verify.
5. Update counts (21/19 → 20/18) and AXIOM_AUDIT.

After this discharge, the only project-introduced axiom on the branch
toward cylinder OS0/OS1/OS2/OS3 is
`asymInteracting_expMoment_volume_uniform` (the §4 cylinder
transfer-matrix-gap input — the genuine deep one).
