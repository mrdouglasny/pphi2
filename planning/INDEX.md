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
  status: **in_progress (this session)**   deps: [17]   diff: ★★★
  note: transfer-matrix Feynman–Kac route. DONE & axiom-clean: dictionary (merged), `TransferSystem`
  instance (merged), energy factorization, GaussianField density bridge (merged), measure
  factorization, abstract B4 engine (merged), operator↔kernel link. REMAINING: the Hilbert–Schmidt
  trace-bridge layer + B5b single-slice stability. Plans: [`docs/B4B5-design.md`],
  [`docs/transfer-instantiation-plan.md`], [`docs/layer-B2-discharge-plan.md`].

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
- [~] **9. `continuumLimit_nonGaussian`** (`u₄≠0`) — **T² version PROVED modulo 1 weak-coupling axiom**   deps: [u₄ step I+III]   diff: ★★★
  note: **`torus_pphi2_isInteracting_weakCoupling`** (`TorusInteractingResult.lean`) is a THEOREM:
  `∃ m₀, ∀ mass>m₀, the genuine T² limit μ is IsTorusPphi2Limit ∧ TorusIsInteracting`. Reduces to
  **one** documented, Gemini-vetted, weak-coupling axiom `torus_weakCoupling_lattice_connectedFourPoint_strictNeg`
  (uniform strict lattice `u₄≤−c<0` for `g<g₀`). **All scaffolding PROVED, axiom-clean:** step IV
  moment convergence (`torus_connectedFourPoint_tendsto`, `TorusInteractingMoments.lean`);
  field-redefinition (`interactingMeasure_map_measurableEquiv` + moment-level `u₄((c•·)_*μ)=c⁴u₄(μ)`,
  `FieldRedefinition.lean`); the free baseline `connectedFourPoint_gaussianMeasure_eq_zero` (`u₄=0`,
  the `g=0` anchor). **Remaining = discharge the 1 axiom** (perturbative `u₄`): step I (Wick
  `u₄'(0)=−6∫(C_a f)⁴`, the connected-correlator derivative — coupled to the leading-term *operator*
  setup `C_a f`), step II (`∫(C_a f)⁴>0`), step III (Nelson `O(g²)` remainder — the crux). The
  multi-week analytic core; the anchor is its first landed brick. (ℝ² version additionally needs the
  `L→∞` cluster expansion — out of scope.)

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

## Plan-loop frontier — 2026-06-05 (post T²-interacting build-out)

Major progress this session on the **non-triviality / interacting** axis (items 9, 11):
`torus_pphi2_isInteracting_weakCoupling` is now a **theorem** (the T² φ⁴₂ theory is interacting at
weak coupling) reducing to **one** documented weak-coupling axiom; all its scaffolding is proved &
axiom-clean (step-IV moment convergence, the field-redefinition layer, the free-field `u₄=0` anchor).

**The plan-loop has reached the research frontier.** Every remaining item is one of a small set of
★★★ analytic mountains (each a multi-week formalization) or a human-judgement call — there are no
cheap actionable increments left:
- **u₄ perturbative discharge** (item 9's last axiom): steps I (Wick connected-correlator derivative
  + leading-term operator setup) + III (Nelson cutoff-uniform remainder). Anchor landed; the rest is
  the analytic core.
- **S₂>0 continuum nondegeneracy** (item 11): short-distance singularity / cluster expansion (the
  FKG route is wrong-direction, vetted).
- **Spectral gap uniformity** (16/17), **clustering square dictionary** (14/15), **Nelson/Lee–Yang**
  (2/12), **rotation defect** (13), **IR-limit** (10), **cluster-expansion keystone** (4/18) — all
  ★★★ or human-gated, per the 2026-06-04 triage above (unchanged).

Net: the architecture is complete and the remaining content is isolated into documented, vetted
axioms; discharging any one of them is a standalone research-grade subproject. The plan-loop's
incremental surface is exhausted — further progress = committing to one of these mountains.

## Staleness flags
Many `docs/*` plans predate the transfer-matrix pivot (several dated 2026-05-13). The CURRENT
status for Layer B2 (3) and the transfer route is `docs/B4B5-design.md` +
`docs/transfer-instantiation-plan.md` (refreshed 2026-06-04). `docs/AXIOM_STATUS.md` and
`docs/axiom_proof_plans.md` are the prior consolidation attempts — this index supersedes them as
the master status machine; refresh those or fold them in.
