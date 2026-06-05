# pphi2 — remaining-axiom discharge plan (master index)

**Plan-loop status machine for the 17 project-introduced axioms** standing between the current
state and "φ⁴₂ is a Wightman QFT, in Lean." Single source of truth: this file. Each row points to
the canonical detailed discharge plan (in `docs/`); where the detailed plan is stale or missing,
that is flagged. Re-read this index every cycle; pick the next `todo`/`in_progress` item whose
`deps` are `done`.

Status legend: `done` = proved/sorry-free · `in_progress` = actively being formalized ·
`scoped` = discharge route designed, not started · `open` = route not yet pinned.
Difficulty: `★` mechanical/short · `★★` real but bounded · `★★★` genuine hard analytic core.

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

- [ ] **16. `spectral_gap_lower_bound`** `TransferMatrix/SpectralGap.lean:100`   status: scoped   deps: []   diff: ★★★
  note: explicit lower bound on the cylinder mass gap, uniform in the continuum limit. Plan:
  [`docs/transfer-matrix-and-mass-gap.md`], [`docs/cyl-2-scope.md`].
- [ ] **17. `spectral_gap_uniform`** `TransferMatrix/SpectralGap.lean:89`   status: scoped   deps: []   diff: ★★★
  note: the gap survives `a→0` / volume limit (THE other hard core; the asym finite-`a` gap
  `asymGappedTransfer'` is PROVED — uniformity in the limit is what remains). Plans:
  [`docs/cyl-2-scope.md`], [`docs/cylinder-conditional-inputs-provability.md`], [`docs/gemini_review.md`].
- [ ] **14. `two_point_clustering_from_spectral_gap`** `OSProofs/OS4_MassGap.lean:137`   status: scoped   deps: [17]   diff: ★★
  note: exponential clustering of the 2-pt function from the gap. Plan: [`docs/cyl-2-scope.md`].
- [ ] **15. `general_clustering_from_spectral_gap`** `OSProofs/OS4_MassGap.lean:160`   status: scoped   deps: [17]   diff: ★★
  note: OS4 clustering for general observables. Plan: [`docs/cyl-2-scope.md`].

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

- [ ] **9. `continuumLimit_nonGaussian`** `ContinuumLimit/Convergence.lean:256`   status: open   deps: []   diff: ★★★
  note: the continuum limit is NOT Gaussian (non-vanishing connected 4-pt / Ursell function).
  Essential — without it the construction yields the free field. Plan:
  [`docs/lattice-action-normalization-fix.md`], [`docs/axiom_proof_plans.md`].
- [ ] **11. `pphi2_nontriviality`** `Main.lean:128`   status: open   deps: [9]   diff: ★★★
  note: top-level non-triviality of the φ⁴₂ theory. Plan:
  [`docs/polynomial-chaos-concentration.md`], [`docs/axiom_proof_plans.md`].

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

## The three genuine mountains (★★★, mostly independent)

1. **The exp-moment chain** (1←2←12, +3) — Layer A (Nelson/Lee–Yang) + Layer B2 (transfer gap, ours).
2. **The uniform spectral gap + clustering** (16, 17 → 14, 15) — the OS4 mass gap surviving the limit.
3. **Non-triviality** (9, 11) — the limit is interacting, not free.
Plus **rotation restoration** (13) for OS2. Everything else (4, 5, 6, 7, 8, 10) is ★/★★
"estimate-and-pass-to-limit" once the mountains land.

## Staleness flags
Many `docs/*` plans predate the transfer-matrix pivot (several dated 2026-05-13). The CURRENT
status for Layer B2 (3) and the transfer route is `docs/B4B5-design.md` +
`docs/transfer-instantiation-plan.md` (refreshed 2026-06-04). `docs/AXIOM_STATUS.md` and
`docs/axiom_proof_plans.md` are the prior consolidation attempts — this index supersedes them as
the master status machine; refresh those or fold them in.
