# Axiom Status Snapshot

*Current state of pphi2's axiom inventory. No history — see
[`axiom_audit.md`](axiom_audit.md) for the historical log of audit
passes and discharges. Last refreshed: 2026-05-10.*

## At a glance

| Count | Value |
|---|---|
| pphi2 axioms (active) | **17** (15 public + 2 `private`) |
| pphi2 sorries | **3** (all in `RoughErrorBound.lean`, all en route to `rough_error_variance`): `canonicalCrossTerm_inner_eq_zero` (S3 cross-term orthogonality; gaussian-field's `gff_wickPower_two_site_inner` (now axiom-free at 8705a13) handles the lattice GFF case — for the canonical-setup adaptation see [`canonical-2site-wick-formula-plan.md`](canonical-2site-wick-formula-plan.md)); `canonicalCrossTerm_l2_sq_le` (S4 per-cross-term L² bound, needs upstream Glimm-Jaffe Phase B + diagonal canonical 2-site Wick); `rough_error_variance` (main theorem, S5 assembly given S3 + S4). S1, S2, full S3 composition (`canonicalRoughError_l2_sq_eq`) all proved structurally. |
| `lake build` | clean (3803 jobs) |
| Direct upstream deps | gaussian-field (`269fbc2`, 3 axioms / 0 sorries), markov-semigroups (`3cb482d`, 11 axioms / 0 sorries), gaussian-hilbert (`05ee231`, 4 axioms / 0 sorries), bochner (`main`) |

The `scripts/count_axioms.sh` script reports 19 because of two
`axiom`-prefixed words in docstrings at `LatticeBridge.lean:21` and
`LayerCake.lean:85`. The actual count is 17.

### Conventions

Audit-table conventions per
[`research-dev/library/lean/AXIOM_MANAGEMENT.md`](https://github.com/mrdouglasny/research-dev/blob/main/library/lean/AXIOM_MANAGEMENT.md)
§2:

| Sources | Meaning |
|---|---|
| `GR` | External Gemini review (chat-mode) |
| `DT` | Gemini deep think verification |
| `SA` | Self-audit (agent's own assessment) |
| `PR` | Peer review (another human or agent) |
| `LP` | Literature proof (cited theorem with page number) |

| Rating | Meaning |
|---|---|
| `Standard` | Well-known fact, correctly stated |
| `Likely correct` | Mathematically sound, needs type/quantifier check |
| `Needs review` | Potentially problematic or non-standard formulation |
| `Placeholder` | Conclusion is `True`, trivially weak, or a research endpoint |
| `Flagged` | Known issue identified by review |

## Critical-path axioms

### T² interacting OS theory (`torusInteracting_satisfies_OS`, OS0–OS4 on T²)

Verified via `#print axioms`: **1 non-builtin axiom**.

| Axiom | File | Discharge plan | Effort |
|---|---|---|---|
| `polynomial_chaos_exp_moment_bridge` | `NelsonEstimate/PolynomialChaosBridge.lean:116` | [`polynomial-chaos-exp-moment-bridge-proof-plan.md`](polynomial-chaos-exp-moment-bridge-proof-plan.md) (parent) + [`rough-error-variance-plan.md`](rough-error-variance-plan.md) (Step 1, rev 2 + Gemini DT review) + [`rough-error-variance-deep-think-review.md`](rough-error-variance-deep-think-review.md) (review record) | ~2-3 weeks total + 3 upstream sorries (Glimm-Jaffe Ch. 8 Fourier estimates + measure-theory factorization) |

After this discharge, 3 transitive OU placeholders from gaussian-hilbert
will appear in `torusInteracting_satisfies_OS`'s axiom set; those have
their own plan: [`gaussian-hilbert/docs/ou-mehler-discharge-plan.md`](https://github.com/mrdouglasny/gaussian-hilbert/blob/main/docs/ou-mehler-discharge-plan.md) (~3-4 weeks).

### T² Gaussian (free-field) OS theory (`torusGaussianLimit_satisfies_OS`)

Verified via `#print axioms`: **0 non-builtin axioms**. Fully proved.

### Flat-ℝ² S'(ℝ²) continuum theory (alternative target)

| Axiom | File | Discharge plan | Effort |
|---|---|---|---|
| `latticeGreenBilinear_basis_tendsto_continuum` | `GaussianContinuumLimit/PropagatorConvergence.lean:103` | [`lattice-green-flat-Rd-discharge-plan.md`](lattice-green-flat-Rd-discharge-plan.md) (Strategy A) | ~3 weeks |

NOT on the T² critical path. Only needed if the project pushes to flat-ℝ²
S'(ℝ²) Wightman directly.

## Full axiom inventory

### Bridge / phase-6 (5 axioms — pphi2 ↔ φ⁴ classification)

| Axiom | File:Line | Rating | Sources | Notes |
|---|---|---|---|---|
| `measure_determined_by_schwinger` | `Bridge.lean:229` | Likely correct | DT 2026-02-24 | Moment determinacy via Fernique-type bound. |
| `schwinger_agreement` | `Bridge.lean:263` | Likely correct | DT 2026-02-24 | n-point Schwinger function equality at weak coupling. |
| `os2_from_phi4` | `Bridge.lean:334` | Likely correct | DT 2026-02-24 | Requires `IsPhi4ContinuumLimit`. |
| `wick_constant_comparison` | `Bridge.lean` | Standard | DT 2026-02-24 | Wick constant `≈ (2π)⁻¹ log(1/a) + bounded`. |
| `pphi2_nontriviality` | `Main.lean:128` | Placeholder | — | Phase-4 research endpoint: bridge to φ⁴; downstream of `same_continuum_measure`. |

### Continuum-limit machinery (3 axioms — abstract Mitoma/Prokhorov chassis)

| Axiom | File:Line | Rating | Sources | Notes |
|---|---|---|---|---|
| `continuum_exponential_moment_bound` | `ContinuumLimit/AxiomInheritance.lean:123` | Likely correct | SA 2026-04-19 | Design bridge: mixed `L¹`/Green `∫ exp(\|ωf\|) dμ ≤ exp(c₁∫\|f\| + c₂ G(f,f))`. |
| `canonical_continuumMeasure_cf_tendsto` | `ContinuumLimit/AxiomInheritance.lean:327` | Likely correct | SA 2026-04-19 | Design bridge: coupled UV/IR, CF convergence along `aₙ → 0`, `Nₙ aₙ → ∞`. |
| `continuum_exponential_clustering` | `ContinuumLimit/AxiomInheritance.lean:354` | Likely correct | GR 2026-03-07 | Correct for P(Φ)₂; spectral-gap input for continuum OS4. |
| `continuumLimit_nonGaussian` | `ContinuumLimit/Convergence.lean:256` | Placeholder | — | Phase-4 research endpoint: nontriviality of the limit. |

### Cluster A — Nelson exponential estimate (1 axiom — bridge)

| Axiom | File:Line | Rating | Sources | Notes |
|---|---|---|---|---|
| `polynomial_chaos_exp_moment_bridge` | `NelsonEstimate/PolynomialChaosBridge.lean:116` | Standard | DT 2026-05-08, DT 2026-05-10 | **The T² interacting OS critical-path axiom.** Over-stated to `∀ a > 0` but textbook GJ Ch. 8 covers `a ≤ 1`; large-`a` regime trivial. Plans: [parent](polynomial-chaos-exp-moment-bridge-proof-plan.md), [Step 1](rough-error-variance-plan.md) (rev 2 incorporates Gemini DT 2026-05-10 critique: K-quantifier hygiene, m=1 L¹×L^∞ bound replacing C-S, m≥2 L^m sum bound replacing ‖C_R‖_∞, RHS = `K·T·(1+|log T|)^{P.n−1}`, three named upstream sorries for parallel-tracked Glimm-Jaffe Ch. 8 Fourier estimates). [Review record](rough-error-variance-deep-think-review.md). |

### Spectral gap / mass gap (4 axioms)

| Axiom | File:Line | Rating | Sources | Notes |
|---|---|---|---|---|
| `spectral_gap_uniform` | `TransferMatrix/SpectralGap.lean:89` | Standard | LP | Spectral gap of transfer matrix uniform in lattice size. |
| `spectral_gap_lower_bound` | `TransferMatrix/SpectralGap.lean:100` | Standard | LP | Reed-Simon XIII.12 (cited in CLAUDE.md). |
| `two_point_clustering_from_spectral_gap` | `OSProofs/OS4_MassGap.lean:137` | Standard | — | Standard reconstruction theorem. |
| `general_clustering_from_spectral_gap` | `OSProofs/OS4_MassGap.lean:160` | Standard | — | n-point version. |

### OS proofs (2 axioms)

| Axiom | File:Line | Rating | Sources | Notes |
|---|---|---|---|---|
| `rotation_cf_defect_polylog_bound` | `OSProofs/OS2_WardIdentity.lean:614` | Likely correct | SA 2026-04-19 | Polylog `a²` defect bound for `rotationCFDefect`, uniform in N. Replaces stronger pointwise formulation. |
| `gaussian_rp_cov_perfect_square` (`private`) | `OSProofs/OS3_RP_Lattice.lean:648` | Standard | SA | Covariance form is a perfect square (Gaussian RP technical). |

### Flat-ℝ² Gaussian continuum (1 axiom — alternative target)

| Axiom | File:Line | Rating | Sources | Notes |
|---|---|---|---|---|
| `latticeGreenBilinear_basis_tendsto_continuum` | `GaussianContinuumLimit/PropagatorConvergence.lean:103` | Standard | SA | Spectral lattice Green bilinear → continuum on basis pairs. **Plan**: [`lattice-green-flat-Rd-discharge-plan.md`](lattice-green-flat-Rd-discharge-plan.md) (Strategy A, ~3 weeks). NOT on T² critical path. |

### AsymTorus (1 axiom)

| Axiom | File:Line | Rating | Sources | Notes |
|---|---|---|---|---|
| `asymTorusInteracting_exponentialMomentBound` (`private`) | `AsymTorus/AsymTorusOS.lean:852` | Standard | — | BC-limit lift of the lattice exp-moment bound to the asymmetric-torus continuum measure. Sister of Cluster A but structurally different (BC convergence). |

## Upstream axiom counts (transitively imported)

For full transitive axiom dependencies of pphi2's main theorems via
`#print axioms`, see
[`.lake/packages/«gaussian-hilbert»/docs/AXIOM_AUDIT.md`](https://github.com/mrdouglasny/gaussian-hilbert/blob/main/docs/AXIOM_AUDIT.md)
and [`.lake/packages/MarkovSemigroups/docs/AXIOM_AUDIT.md`](https://github.com/mrdouglasny/markov-semigroups/blob/main/docs/AXIOM_AUDIT.md).

| Repo | Axioms | Plan-coverage |
|---|---|---|
| pphi2 | 17 | 3 critical-path axioms have detailed plans (`polynomial_chaos_exp_moment_bridge` + 1 sub-doc; `latticeGreenBilinear_basis_tendsto_continuum`); rest are textbook items with literature citations |
| gaussian-hilbert | 4 | All 4 plan-covered: 1 (`polynomial_dense_L2_of_subGaussian`) is DT-vetted Standard; 3 (OU placeholders) covered by `ou-mehler-discharge-plan.md` |
| markov-semigroups | 11 | All textbook with literature refs in `AXIOM_AUDIT.md`; no near-term discharge plans (long-term debt) |
| gaussian-field | 3 | Down from 8 after the 2026-05-10 cylinder/Hermite discharges + the 2026-05-11 `gff_wickPower_two_site_inner` proof (axiom-free, Janson 2-site Wick formula on lattice GFF). Remaining 3 axioms are Gemini-vetted Standard classical-analysis (embed-L²-uniform-bound, fourier-multiplier-Schwartz, Hermite-Galerkin tendsto). |

## How to update this file

When adding/removing/discharging an axiom:

1. Update the relevant section above with the new file:line, rating, plan link.
2. Run `scripts/count_axioms.sh` to refresh the at-a-glance count.
3. If a critical-path axiom changes status, update the **Critical-path axioms** section.
4. Add a chronological entry to [`axiom_audit.md`](axiom_audit.md) describing what changed and why (this file is the snapshot; that file is the log).
5. If the change affects upstream consumers (lgt, pphi2N, etc.), bump pins in those repos.
