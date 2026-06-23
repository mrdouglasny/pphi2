# pphi2 — remaining-axiom discharge plan (master index)

**Plan-loop status machine for the 17 project-introduced axioms** standing between the current
state and "φ⁴₂ is a Wightman QFT, in Lean." Single source of truth: this file. Each row points to
the canonical detailed discharge plan (in `docs/`); where the detailed plan is stale or missing,
that is flagged. Re-read this index every cycle; pick the next `todo`/`in_progress` item whose
`deps` are `done`.

Status legend: `done` = proved/sorry-free · `in_progress` = actively being formalized ·
`scoped` = discharge route designed, not started · `open` = route not yet pinned.
Difficulty: `★` mechanical/short · `★★` real but bounded · `★★★` genuine hard analytic core.

## ⚠ Cross-cutting coherence (read first) — [`planning/coherence-analysis.md`]

The 17 axioms are individually sound but **do not currently assemble into "an *interacting* φ⁴₂
QFT exists"**. Three architecture gaps (all fixed by one keystone — weak-coupling uniqueness):
- **A.** `SatisfiesFullOS` (OS0–OS4) is satisfied by the **free field** too; non-triviality (11)
  and non-Gaussianity (9) are **separate `∃μ`**, never conjoined with the OS measure. No theorem
  says "the OS measure is interacting."
- **B.** Gap (16/17) + non-Gaussianity (9) hold **only at weak coupling** (phase transition), but
  `pphi2_exists` is stated for **all `P`** with no coupling hypothesis → over-claim. Must thread
  `IsWeakCoupling` (already in `Bridge.lean`) up into the headline.
- **C.** Keystone **missing from the 17**: **weak-coupling uniqueness of the limit** (cluster
  expansion) — glues the separate `∃μ` into one, fixes the regime, and upgrades subsequence → limit.
- [ ] **18. weak-coupling uniqueness** (NEW target) `—`   status: open   deps: [16/17 regime]   diff: ★★★
  note: cluster expansion / Dobrushin uniqueness at weak coupling. The keystone for A+B+C. Then
  restate the headline as `∃ μ, SatisfiesFullOS μ ∧ (∀f≠0,S₂>0) ∧ u₄≠0`. → `coherence-analysis.md`.

## The goal & geometry

T² (compact torus) already has **OS0–OS2**. The **cylinder** `ℝ × S¹_{Ls}` (infinite Euclidean
time) adds **OS3 (reflection positivity)** and **OS4 (clustering / mass gap)** — the gateway to
**OS reconstruction → Wightman QFT**. The two gating analytic estimates are **CYL-1a** (the
`Lt`-uniform exponential-moment bound, gating OS0/OS1) and **CYL-2a** (the uniform spectral gap →
clustering, gating OS4). Master campaign doc: [`docs/cylinder-master-plan.md`].

## Dependency DAG (clusters)

```
                                 nelson_exponential_estimate_master_bounded (12) ★★★
                                              │
   spectral_gap_lower_bound (16) ──┐          ▼
   spectral_gap_uniform (17) ──────┤    asymInteracting_mgf_gaussianDominated (2)  [Layer A]
        │  (CYL-2a) ★★★            │          │
        ▼                          │          ▼          asymInteractingVariance_le_
   two_point_clustering (14) ★★    │   asymInteracting_expMoment_volume_uniform (1) ◄── freeVariance_Lt_uniform (3) [Layer B2, OURS] ★★★
   general_clustering (15) ★★      │          │  [CYL-1a, Layer C assembly] ★
        │ (OS4)                    │          ▼
        ▼                          │   continuum_exponential_moment_bound (6) ★★ ──► OS0/OS1
   continuum_exponential_          │   canonical_continuumMeasure_cf_tendsto (7) ★★
   clustering (8) ★★               │   latticeGreenBilinear_..._continuum (10) ★★
                                   │   continuumLimit_nonGaussian (9) ★★★ ─┐
   rotation_cf_defect (13) ★★★ ───┘   pphi2_nontriviality (11) ★★★ ───────┤► non-triviality
   os2_from_phi4 (5) ★★  [OS2]         schwinger_agreement (4) ★  [OS bridge]
```

---

## Cluster 1 — CYL-1a: the `Lt`-uniform exponential-moment bound (gates OS0/OS1)

- [ ] **1. `asymInteracting_expMoment_volume_uniform`** `AsymContinuumLimit.lean:621`
  status: scoped   deps: [2, 3]   diff: ★ (Layer C assembly, ~50 lines)
  note: `K·exp(C·Var_free)` bound. Assembly of Layer A (2) × Layer B2 (3). Plan:
  [`docs/asym-interacting-expmoment-volume-uniform-discharge-plan.md`], [`docs/cyl-1a-bridge-plan.md`].
- [ ] **2. `asymInteracting_mgf_gaussianDominated`** (Layer A) `AsymExpMomentDischarge.lean:127`
  status: scoped   deps: [12]   diff: ★★★
  note: Newman MGF via Gaussian domination / Lee–Yang. New `lee-yang` repo scaffolded, Phase 1 not
  implemented. Plan: [`docs/asym-expmoment-discharge-via-lee-yang-vet-request.md`].
- [~] **3. `asymInteractingVariance_le_freeVariance_Lt_uniform`** (Layer B2) `AsymExpMomentDischarge.lean:206`
  status: **in_progress — Route A blueprint pinned 2026-06-22, Piece 1 landed**   deps: [17]   diff: ★★★ (★★ with the route pinned)
  note: transfer-matrix Feynman–Kac route, **Route A** (bounded-cutoff approximation, gemini-vetted
  2026-06-22). **Built & sorry-free on `main`** (`Pphi2/AsymTorus/Asym*`):
  the rank-1 operator-decay bricks (`AsymTraceBridge`), the proved gap (`AsymGappedTransfer`,
  `susceptibility_le`), the measure→path-measure bridge `interacting_second_moment_eq_pathMeasure`
  (`AsymVarianceDischarge`, B3), the abstract B4 susceptibility engine, the operator↔kernel link
  (`AsymTransferKernelOperator`), and **Piece 1 of the Route-A wiring**: the truncated-observable
  multiplication CLM + the **a-cancellation lemma** `norm_sq_proj_obsTrunc_omega_le`
  (`Pphi2/AsymTorus/AsymObsTrunc.lean`, landed 2026-06-22). **Live plan:**
  [`planning/layer-B2-scoping.md`] (the Route-A blueprint; 5 pieces; ~600-1200 lines; ~1.5-3 weeks).
  **REMAINING (per Route A blueprint):** Piece 2 — apply `averaged_susceptibility_bound` at finite K
  (~200-300 lines); Piece 3 — `K → ∞` via DCT (~100-200 lines); Piece 4 (B5b) — single-slice
  stability (~200-400 lines, vet `a`-powers first); Piece 5 — final assembly (~50-100 lines).
  SUPERSEDED: [`docs/transfer-instantiation-plan.md`] (banner), the older 6-brick HS-Cauchy-Schwarz
  plan in `docs/B4B5-design.md` (eliminated by Route A — op-norm ≤ HS-norm is the wrong direction).

## Cluster 2 — CYL-2a: uniform spectral gap → clustering (gates OS4)

**Full plan: [`planning/cyl-2a-spectral-gap.md`].** Key findings there: (i) the two clustering
axioms **ride on the B2 trace bridge** — they reduce to the proved `connected_two_point_le`, so
they discharge in the same PR as B2 (★★ given that bridge); (ii) `spectral_gap_uniform/lower_bound`
as stated are **too strong** — φ⁴₂ has a phase transition where the gap closes, so they need a
weak-coupling / single-phase hypothesis.

- [ ] **17. `spectral_gap_uniform`** `TransferMatrix/SpectralGap.lean:89`   status: scoped   deps: []   diff: ★★★
  note: gap survives `a→0` (finite-`a` gap `asymGappedTransfer'` PROVED; continuum uniformity
  remains). **Regime-restricted** (phase transition). Route: `a→0` eigenvalue-gap limit /
  perturbative. THE independent hard core of CYL-2a. → `planning/cyl-2a-spectral-gap.md`.
- [ ] **16. `spectral_gap_lower_bound`** `TransferMatrix/SpectralGap.lean:100`   status: scoped   deps: []   diff: ★★★→★★
  note: `c·mass ≤ massGap` — FALSE at criticality; weak-coupling `m_phys ≥ m − Cλ` via the existing
  Nelson estimates. → `planning/cyl-2a-spectral-gap.md`.
- [ ] **14. `two_point_clustering_from_spectral_gap`** `OSProofs/OS4_MassGap.lean:137`   status: scoped   deps: [3-bridge]   diff: ★★ (given B2 trace bridge)
  note: = `connected_two_point_le` with `γ=e^{−massGap·a}` via `twoPoint_dictionary` +
  `asymTransferKernel_kPow_apply` (proved). Do in the B2 trace-bridge PR. → `planning/cyl-2a-spectral-gap.md`.
- [ ] **15. `general_clustering_from_spectral_gap`** `OSProofs/OS4_MassGap.lean:160`   status: scoped   deps: [3-bridge]   diff: ★★ (given B2 trace bridge)
  note: same, bounded `F,G` → `M_F,M_G`. → `planning/cyl-2a-spectral-gap.md`.

## Cluster 3 — OS2 (rotation invariance)

- [ ] **13. `rotation_cf_defect_polylog_bound`** `OSProofs/OS2_WardIdentity.lean:614`   status: scoped   deps: []   diff: ★★★
  note: lattice breaks rotations; the characteristic-function rotation defect → 0 in the continuum
  limit (polylog bound). Plan: [`docs/cylinder-master-plan.md`], [`docs/dual-construction-strategy.md`].
- [ ] **5. `os2_from_phi4`** `Bridge.lean:345`   status: scoped   deps: [13]   diff: ★★
  note: OS2 (E(2)-invariance) for the φ⁴ measure from the rotation defect bound. Plan:
  [`docs/axiom_proof_plans.md`], [`docs/AXIOM_STATUS.md`].

## Cluster 4 — continuum-limit inheritance

- [ ] **6. `continuum_exponential_moment_bound`** `ContinuumLimit/AxiomInheritance.lean:123`   status: scoped   deps: [1]   diff: ★★
  note: pass the `Lt`-uniform exp-moment (1) to the continuum measure. Plan:
  [`docs/asym-interacting-expmoment-volume-uniform-discharge-plan.md`].
- [ ] **7. `canonical_continuumMeasure_cf_tendsto`** `ContinuumLimit/AxiomInheritance.lean:327`   status: scoped   deps: []   diff: ★★
  note: characteristic-function convergence lattice → continuum. Plan: [`docs/pr10_summary.md`].
- [ ] **8. `continuum_exponential_clustering`** `ContinuumLimit/AxiomInheritance.lean:354`   status: scoped   deps: [14, 15]   diff: ★★
  note: clustering passes to the continuum. Plan: [`docs/cyl-2-scope.md`].
- [ ] **10. `latticeGreenBilinear_basis_tendsto_continuum`** `GaussianContinuumLimit/PropagatorConvergence.lean:103`   status: scoped   deps: []   diff: ★★
  note: free propagator (bilinear form) lattice → continuum on a basis. Plan: [`docs/pr10_summary.md`].
  (Free/Gaussian — likely the most tractable here; cf. the proved `second_moment_asym_tendsto`.)

## Cluster 5 — non-triviality (the limit is genuinely interacting)

**Full plan: [`planning/non-triviality.md`].** The two are very different: 11 is *not*
non-Gaussianity (only `S₂>0`, ★★ via correlation inequalities, all phases); 9 is the genuine
interacting content (`u₄≠0`, ★★★, needs `λ>0`).

- [~] **11. `pphi2_nontriviality`** (`S₂(f,f)>0` for `f≠0`) `Main.lean:128`   status: **MIS-FORMULATED → reformulated on T²**   deps: []   diff: ★★→★★★
  note: The ℝ² axiom is `∃μ,S₂>0` with **P,mass unused** → free-field/δ₀ satisfy it (`IsPphi2Limit`
  itself is δ₀-vacuous; see memory `pphi2-existence-vacuous-delta0`). **Honest version formulated on
  the genuine (axiom-clean-existing) T² theory**: `TorusNontriviality.lean` —
  `IsTorusPphi2Limit` + `torusPphi2Limit_exists` (PROVED), `TorusIsNondegenerate` (S₂>0). ⚠️ Route
  **corrected** (Gemini-vetted, memory `pphi2-s2-domination-direction`): "Griffiths/FKG ⟹ ≥free" is
  **wrong-direction** — continuum nondegeneracy needs short-distance singularity / cluster expansion
  (★★★), not FKG. → `planning/non-triviality.md`.
- [x] **9. `continuumLimit_nonGaussian`** (`u₄≠0`) — **T² non-Gaussianity DONE, AXIOM-FREE (Route A, 2026-06-07)**   deps: []   diff: ★★★
  note: `torus_pphi2_isInteractingStrict_weakCoupling` (`TorusContinuumLimit/TorusCouplingResult.lean`)
  is a THEOREM, `#print axioms ⟹ [propext, Classical.choice, Quot.sound]`: for some small coupling
  `g₀∈(0,1]`, the continuum limit of the coupling-`g₀` interacting torus measures has
  `torusConnectedFourPoint μ (torusOne) < 0` (`TorusIsInteractingStrict`, hence `TorusIsInteracting`).
  The earlier axiom `torus_weakCoupling_lattice_connectedFourPoint_strictNeg` is **NOT used** — Route A
  discharged that content directly (coupling-family continuum limit `A1–A5` + 4-homogeneity `u4_smul`).
  Branch `route-a-weak-coupling` (PR #48); design `planning/route-A-weak-coupling-plan.md`.
  **Still open (separate):** (i) the conventional `λ=1`/large-mass *normalization* — Route B (continuum
  dilation), DEFERRED, needs clustering (`planning/continuum-rescaling-plan.md`); (ii) the **ℝ²**
  (infinite-volume) `continuumLimit_nonGaussian` axiom itself, which additionally needs `L→∞`
  cluster expansion; (iii) conjoining `u₄≠0` with the *same* OS measure + full OS0–OS4 (keystone 18).
  The T² non-Gaussianity *content* is now proved.

## Cluster 6 — OS→Schwinger bridge

- [ ] **4. `schwinger_agreement`** `Bridge.lean:274`   status: scoped   deps: []   diff: ★
  note: the constructed Schwinger functions agree with the measure moments (bookkeeping bridge).
  Plan: [`docs/axiom_proof_plans.md`], [`docs/AXIOM_STATUS.md`].

## Cluster 0 — foundational (feeds Layer A)

- [ ] **12. `nelson_exponential_estimate_master_bounded`** `NelsonEstimate/PolynomialChaosBridge.lean:1321`
  status: scoped   deps: []   diff: ★★★
  note: the Nelson hypercontractivity / polynomial-chaos exponential estimate — the analytic engine
  under Layer A. Plans: [`docs/nelson-bridge-generalization-plan.md`],
  [`docs/degree-piecewise-tail-discharge-plan.md`], [`docs/polynomial-chaos-exp-moment-bridge-proof-plan.md`].

---

## The four genuine ★★★ mountains (mostly independent)

1. **The exp-moment chain** (1 ← 2 ← 12, + 3) — Layer A (Nelson/Lee–Yang) + Layer B2 (transfer gap,
   ours). Status: B2 mostly proved (HS trace-bridge tail); Layer A not started.
2. **The uniform spectral gap** (16, 17) — the OS4 mass gap surviving `a→0`. **Regime-restricted**
   (phase transition). *Independent of B2.* — Note: the **clustering** axioms (14, 15) are NOT a
   separate mountain; they ride on the B2 trace bridge (= `connected_two_point_le`).
3. **Non-Gaussianity** (9, `u₄≠0`) — the limit is genuinely interacting. *Needs `λ>0`.* — Note:
   `pphi2_nontriviality` (11, `S₂>0`) is only ★★, NOT a mountain.
4. **Rotation restoration** (13) for OS2 — the lattice→continuum rotation defect.

Everything else (4, 5, 6, 7, 8, 10, 11, 14, 15) is ★/★★ "estimate-and-pass-to-limit" or rides on a
mountain's infrastructure once it lands.

## Plan-loop triage — cycle 2026-06-04 (the actionable-item sweep)

This cycle investigated the four "cheap independent" candidates (4, 7, 10, 11) to find anything
dischargeable now. **Result: all blocked on a substantial missing lemma** — none is a few-edit win.
Precise blockers (so the next owner starts from the exact gap, not a re-investigation):

- **4 `schwinger_agreement`** — BLOCKED on **keystone 18** (cluster expansion / weak-coupling
  uniqueness). The axiom = "pphi2-lattice and Phi4-continuum Schwinger sequences agree", which is
  exactly the interchange-of-limits the cluster expansion provides. Missing lemma:
  `schwinger_pphi2_eq_phi4_of_weak_coupling`. The `measure_determined_by_schwinger` wrapper is
  already a theorem (2026-06-02); only this agreement input is missing. → deps: [18].
- **7 `canonical_continuumMeasure_cf_tendsto`** — BLOCKED + **needs-human**. Statement is sound in
  form (already couples `N→∞`, `N·a→∞`), but proof needs a non-standard **lattice-realization**
  lemma: *any* `IsPphi2Limit` measure is the weak limit of canonically-coupled `continuumMeasure`s
  (a converse to the continuum limit — unusual; QFT texts only prove lattice→continuum). The
  axiom's self-existential `(N,a)` is decoupled from the abstract limit witness — **review whether
  the axiom should instead be a direct weak-convergence statement** before discharging.
- **10 `latticeGreenBilinear_basis_tendsto_continuum`** — BLOCKED on an **IR-limit theorem**
  (torus box `L→∞` → flat ℝ² Fourier Green). Proved sibling `second_moment_asym_tendsto` /
  `lattice_green_tendsto_continuum_asym` is **torus→torus only**. Missing:
  `ir_limit_continuum_green_tendsto : limₗ asymTorusContinuumGreen L = continuumGreenBilinear`.
  Then dominated convergence + DM nuclear extension finishes. Flagged **not on the T² critical
  path** (~3 wk standalone). → deps: [IR-limit].
- **11 `pphi2_nontriviality` (S₂>0)** — **actionable cheaply, but a project-intent decision.**
  Step 1 (free positivity) is **PROVED**: `gaussianContinuumLimit_nontrivial` (GaussianLimit.lean:102)
  exhibits a free-field continuum-limit measure with `∀f≠0, S₂(f,f)>0` — which **already witnesses
  the axiom as literally stated** (`∃μ, …`). So the axiom is dischargeable NOW via the free field.
  BUT that conflicts with intent (coherence Gap A: we want S₂>0 for the *interacting* μ). The
  genuine route (step 2, Griffiths/FKG `S₂^int ≥ S₂^free`) is **missing** — FKG infra exists
  (`Lattice/FKG.lean`, proved) but is not applied to two-point monotonicity-in-coupling; pphi2's
  Nelson bound (`asymInteractingVariance_le_freeVariance_lattice`) is an *upper* bound (wrong
  direction for a lower bound). → **human decision: cheap free-field discharge vs. keep open for
  the interacting result.**

**Clustering 14/15 reassessment** (was "★★ given the B2 trace bridge"): the B2 dictionary
(`twoPoint_dictionary`) exists **only on the asym torus**; 14/15 are stated on the **square**
`FinLatticeField 2 Ns`. The square lattice has transfer infra (`Pphi2/TransferMatrix/*`) but **no
square `twoPoint_dictionary` and no square `GappedTransfer` packaging**. So 14/15 are BLOCKED on
**building the square trace dictionary** (port the asym B2/B4 chain to the square, or prove
asym↔square at `Nt=Ns`) — a substantial step, not a few edits. → deps: [square-trace-dictionary].

**Net:** the lone genuinely-unblocked formalization thread is **item 3's own deliverable** (the asym
variance bound) via the asym dictionary + the operator bricks 0–2 (proved this session) +
`connected_susceptibility_le`. Everything else is blocked on one of: keystone 18 (cluster
expansion), the IR-limit theorem, FKG two-point domination, the square trace dictionary, the
Layer-A Nelson/Lee–Yang engine (2/12), the spectral-gap-uniformity (17), or a regime/intent human
decision (11, 16/17/9, 7).

## Plan-loop frontier — 2026-06-07 (post Route-A non-triviality)

**Item 9 (non-Gaussianity, `u₄≠0`) is DONE on T², axiom-free** (Route A,
`torus_pphi2_isInteractingStrict_weakCoupling`, PR #48). The earlier weak-coupling axiom is not used.
That clears one of the four ★★★ mountains for the T² content and means **the cylinder no longer has to
carry non-triviality** — its job is purely OS3/OS4.

**Active focus: the cylinder (Route B′), Layer B2 (item 3).** The transfer-matrix machinery is built
and sorry-free on `main`; the remaining gap is wiring B3→B4→B5 (trace dictionary on the path-measure
second moment + HS trace-class + B5b single-slice stability + the `1/a` cancellation). Live plan:
[`docs/B4B5-design.md`]. This is the nearest concrete win.

Remaining ★★★ mountains / human-gated items (unchanged from the 2026-06-04 triage):
- **Layer A** (`asymInteracting_mgf_gaussianDominated`, item 2) — Newman MGF via Lee–Yang; not started.
- **Spectral gap uniformity** (16/17) — also feeds OS4 clustering (14/15) *and* the deferred Route B.
- **S₂>0 continuum nondegeneracy** (item 11) — short-distance singularity / cluster expansion.
- **Nelson/Lee–Yang** (12), **rotation defect** (13), **IR-limit** (10), **cluster-expansion
  keystone** (4/18).

Net: the architecture is complete; non-Gaussianity on T² is now a theorem. The incremental surface is
the cylinder Layer-B2 wiring (item 3); everything else is a standalone research-grade subproject.

## Axioms beyond the 17 (sanity check vs `count_axioms.sh`)

`count_axioms.sh` reports **28 raw axioms** on `layer-B2/piece-2` (rechecked 2026-06-23);
3 are docstring matches of the word "axiom" inside text continuations
(`Pphi2/NelsonEstimate/LatticeBridge.lean:21`,
`Pphi2/NelsonEstimate/LayerCake.lean:85`,
`Pphi2/AsymTorus/AsymExpMomentDischarge.lean:244`), leaving **25 real axioms**.

The 23 architectural axioms account for the current proof debt, including the
six Layer-B2 Route-A GNS bridge obligations in
`Pphi2/AsymTorus/AsymBridgeInstance.lean`:
`asymGroundStateRep_pos_ae`, `asymTransferNormalized_contract`,
`asymGroundStateRep_eq_groundIsometry_one`, `asymGroundSemigroup_intertwines`,
`asymPartition_ground_bound`, and `asymFinitePeriodicBridge_remainder_bound`.
The remaining 2:
- **`asymTorusInteracting_exponentialMomentBound`** (`Pphi2/AsymTorus/AsymTorusOS.lean`,
  `private`) — torus-side scaffolding consumed only inside `AsymTorusOS`.
- **`gaussian_rp_cov_perfect_square`** (`Pphi2/OSProofs/OS3_RP_Lattice.lean`,
  `private`) — covariance-perfect-square step inside lattice-RP.

The superseded-chain `torus_weakCoupling_lattice_connectedFourPoint_strictNeg` axiom
(added 2026-06-05) and its sole consumer `torus_pphi2_isInteracting_weakCoupling`
(carrier file `Pphi2/TorusContinuumLimit/TorusInteractingResult.lean`) were **removed on
2026-06-21** after Route A's `torus_pphi2_isInteractingStrict_weakCoupling`
(2026-06-07, PR #48) subsumed them.

## Branch map
For which git branch carries the live code for each axiom (and which branches are
superseded/dormant), see [`BRANCHES.md`](../BRANCHES.md) at the repo root. Quick pointers as of
2026-06-07: axiom 9 (u₄ non-Gaussianity) → **DONE, axiom-free** on `route-a-weak-coupling` (PR #48);
axiom 3 (variance / Layer-B2, the cylinder's active item) → `main`. SUPERSEDED/dormant:
`option-b-feynman-kac` + `docs/transfer-instantiation-plan.md` (transfer route, replaced by the
`main` Asym* files + `docs/B4B5-design.md`); `l5-affine-bound` (the lattice u₄ route, subsumed by
Route A); `planning/continuum-rescaling-plan.md` (Route B, deferred).

## Staleness flags
Many `docs/*` plans predate the transfer-matrix pivot (several dated 2026-05-13). The CURRENT
status for Layer B2 (3) and the transfer route is `docs/B4B5-design.md` (NB
`docs/transfer-instantiation-plan.md` is now SUPERSEDED — see its banner). `docs/AXIOM_STATUS.md`
and `docs/axiom_proof_plans.md` are the prior consolidation attempts — this index supersedes them as
the master status machine; refresh those or fold them in. Dated hand-off/snapshot docs and the
plans for the now-proved `rough_error_variance` axiom were moved to `docs/archive/` on 2026-06-07.
