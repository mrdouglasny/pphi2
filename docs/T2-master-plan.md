# T² φ⁴₂ continuum limit — master plan & progress tracker

**Last refreshed:** 2026-05-22 (**✅ ENDPOINT NOW AXIOM-FREE — bare Mathlib trio.** `#print axioms Pphi2.torusInteracting_satisfies_OS` = `[propext, Classical.choice, Quot.sound]`, verified on pphi2 `main` after bumping pins to gh `7627451` / ms `e6b8a77` (clean 3904-job build). All four Gross-chain axioms — `gross_lsi_implies_hypercontractive`, `stroock_varopoulos`, `gaussianFin_integrationByParts`, `gaussianFin_diffQuot_tendsto_Lp` (the last via the now-proved pointwise OU heat equation + L²-DCT) — are discharged and propagated to the endpoint. The M-goal of this document is reached. The discharge route: all four Gross hypotheses for the GaussianFin/OU instance in ms `EuclideanHypercontractive.lean` → `stdGaussianFin_isHypercontractive` via the proved `gross_lsi_implies_hypercontractive_of_hypotheses` (ms PR #5); `stroock_varopoulos` via the diffusion equality `BakryEmerySpace.stroockVaropoulos_eq` (ms PR #7, `Diffusion/StroockVaropoulos.lean`); `gaussianFin_integrationByParts` via the Fubini lift of the proved 1D IBP (ms PR #10); `gaussianFin_diffQuot_tendsto_Lp` via the pointwise OU heat equation (ms PR #11) + L²-DCT (ms PR #12). Prior (2026-05-21): abstract Gross spine merged at `5d09d4a` via PR #3.)
**Repo:** pphi2 (this) + sister repos gaussian-hilbert, markov-semigroups
**Endpoint:** `Pphi2.torusInteracting_satisfies_OS` (OS0 + OS1 + OS2 for the T²_L
symmetric-torus φ⁴₂ continuum limit)
**Branch:** `main` (all three repos are now single-active-branch on `main` after
the 2026-05-17 consolidation; the prior feature branches are preserved as
`archive/*` tags — see "Branch state" below)

This document is the **single source of truth** for the T² OS0–OS2 endpoint
campaign. It tracks the five workstreams that, when complete, reduce the
endpoint's axiom closure to `[propext, Classical.choice, Quot.sound]`
only. Per-workstream details and proof plans live in their dedicated docs
(linked from each row below).

---

## Current closure — ✅ AXIOM-FREE (bare Mathlib trio, realized at the pphi2 endpoint 2026-05-22)

**Verified `#print axioms Pphi2.torusInteracting_satisfies_OS` on pphi2
`main` after bumping pins to gh `7627451` / ms `e6b8a77` + clean 3904-job build:**

```
[propext, Classical.choice, Quot.sound]            ← Mathlib trio ONLY
```

**The T² OS0–OS2 endpoint now rests on the bare Mathlib trio — every non-standard
axiom on the path is discharged.** This is the M-goal of this document (reduce the
endpoint closure to `[propext, Classical.choice, Quot.sound]`). The four non-trivial
Gross-chain axioms were all discharged this session and propagated to the endpoint:

- **Gross** `gross_lsi_implies_hypercontractive` — eliminated (ms PR #5): the four
  predicates `CoreSemigroupInvariant` / `GeneratorCompat` / `StroockVaropoulos` /
  `CoreLpL2Approx` discharged for GaussianFin in `EuclideanHypercontractive.lean`,
  assembled via the proved `…_of_hypotheses` into `stdGaussianFin_isHypercontractive`.
- **Stroock–Varopoulos** `stroock_varopoulos` — eliminated (ms PR #7): the new
  `Diffusion/StroockVaropoulos.lean` proves S–V as an **equality** for any diffusion
  form (`BakryEmerySpace.RpowChainRule` ⇒ `stroockVaropoulos_eq`); `GaussianFin.rpowChainRule`
  discharges it for `ouGammaFin` via `partialDeriv_rpow`.
- **IBP** `gaussianFin_integrationByParts` — eliminated (ms PR #10): coordinatewise
  Fubini lift of the proved 1D `Gaussian1D.gaussian_dirichlet_form_bilinear`.
- **Strong-L² difference quotient** `gaussianFin_diffQuot_tendsto_Lp` — eliminated
  (Step A ms PR #11: pointwise OU heat equation `gaussianOU_heatEquation_within_zero`
  as an nD lift of the 1D `hasDerivAt_t_ouSemigroup'`; Step B ms PR #12: L²-dominated
  convergence from the pointwise limit with an affine-in-`‖x‖₁` L² dominator).

(N1.b `ouSemigroupFin_preserves_IsCore` and N1.c `ouSemigroupFin_entropy_sq_decay_bound`
were discharged to axiom-free theorems earlier, so they never appeared in the closure.)

**Pin chain that realized it:** ms `main` `e6b8a77` → gh `main` `7627451` (gh PR #4) →
pphi2 pins bumped (force-cleared dep `.lake/build` caches, clean 3904-job build).

**Propagation path that realized this (2026-05-19):**
- ms `main`: `bd7f950` (2.5 + N1.b + N1.c, all axiom-free) → `6293402`
  (restored the `stdGaussianFin_dirichletMarkovSemigroup` bundle the
  2.5 commit had dropped from `EuclideanFinLp.lean`; re-homed into
  `EuclideanFinBE.lean`, 3 helper lemmas de-privatized). Pushed.
- gaussian-hilbert `main`: `2df8345` → `4ac0667` (ms pin → `6293402`;
  `HypercontractivityFromBE.lean` import `EuclideanFinLp` →
  `EuclideanFinBE`). Build green (3245 jobs); pushed.
  `#print axioms GaussianHilbert.polynomial_chaos_concentration` =
  trio + Gross + 2 G2 (no `sorryAx`).
- pphi2 `main`: pins → gh `4ac0667` + ms `6293402`. Clean 3900-job
  build; endpoint closure verified as above.

**M1, M2, M3 — and the full axiom-free M-goal — realized in the pphi2 endpoint
(2026-05-22).** No non-standard axioms remain on the T² OS0–OS2 path:
`gross_lsi_implies_hypercontractive`, `stroock_varopoulos`,
`gaussianFin_integrationByParts`, and `gaussianFin_diffQuot_tendsto_Lp` have all been
discharged and propagated, so the endpoint prints the bare Mathlib trio.

**Lessons recorded:** the 2.5 commit was an under-reviewed breaking
refactor (deleted a committed downstream-consumed bundle with no
adapter/flag); and lake does **not** invalidate dependency `.olean`
caches on a git-pin change — cross-repo pin bumps must force-clear
`.lake/packages/<dep>/.lake/build` before rebuilding, else stale-cache
phantom errors. See project memory.

---

## Branch state — consolidated 2026-05-17

All three repos are now single-active-branch on `main`. The prior
feature branches (`phase-b-discharge` in pphi2, `phase-3-smoke-test` in
gaussian-hilbert, `feat/lp-carrier-stdGaussianFin-dirichletmarkov` in
markov-semigroups) have been merged into their respective `main`s and
preserved as `archive/*` tags. The pin-chain fragmentation flagged in
prior revisions of this doc is **resolved**.

| Repo | Active branch | HEAD | Pins ms at | Archive tags |
|---|---|---|---|---|
| **pphi2** | `main` | pin-bump commit (gh `7627451` + ms `e6b8a77`) — **endpoint axiom-free (bare trio)** | `e6b8a77` | 9 `archive/*` tags (incl. `archive/phase-b-discharge`, `archive/pr10`, …) |
| **gaussian-hilbert** | `main` | `7627451` (ms pin → `e6b8a77`; chain axiom-free) — pushed | `e6b8a77` | `archive/phase-3-smoke-test` |
| **markov-semigroups** | `main` | `e6b8a77` (W-step + S–V + IBP + heat-eq/diffQuot discharges; `Diffusion/StroockVaropoulos.lean`) — pushed | — | `archive/feat/lp-carrier-stdGaussianFin-dirichletmarkov` |

**Pin chain propagated 2026-05-22 (all four Gross-chain axioms discharged).**
markov-semigroups `main` advanced to `e6b8a77`, gaussian-hilbert to `7627451`,
and pphi2 bumped both pins (force-clearing the dep `.lake/build` caches), so the
**pphi2 endpoint is now axiom-free** (bare Mathlib trio).

**pphi2 pin state on main (PROPAGATED 2026-05-22):**
- gaussian-hilbert: `7627451` (ms pin `e6b8a77`; GaussianFin Gross chain axiom-free)
- MarkovSemigroups: `e6b8a77` (W-step + `Diffusion/StroockVaropoulos.lean` + IBP-as-theorem + heat-eq/diffQuot theorems)
- GaussianField: `269fbc2e`
- bochner: `b70e84b8`

`lake build` is clean on pphi2 `main` (**3904 jobs**) as of 2026-05-22 with the
bumped pins. Endpoint closure verified = **`[propext, Classical.choice, Quot.sound]`**
(bare Mathlib trio — see "Current closure"). The pphi2 manifest pin-bump commit also
carries this doc update.

---

## Complete axiom-and-sorry inventory on the T² OS0–OS2 critical path

This is the **comprehensive** list of every axiom and sorry that has
to be closed to get `torusInteracting_satisfies_OS` to the Mathlib trio
only. Each row links to its discharge plan / workstream.

### Sorries on the T² OS0–OS2 critical path

**None.** Pphi2's active build has zero `sorry` tactics; the
grep matches in `TorusInteractingOS.lean`, `TorusGaussianLimit.lean`,
`TorusTightness.lean`, `RoughErrorBound.lean` are docstring fragments
("modulo 2 sorry's", "S3 is the gating sorry", etc.) describing
historical or hypothetical states, **not live `sorry` tactics**.
Verified 2026-05-17 on `main`.

### Axioms on the T² OS0–OS2 critical path

**State (a) — what pphi2 `main` prints today** (pre-2.5 pin `c6e0e6b`,
post-Workstream-B 2026-05-18). 4 inherited axioms:

| Axiom | Location | Workstream / discharge plan |
|---|---|---|
| `gross_lsi_implies_hypercontractive` (legacy abstract axiom) | `markov-semigroups/MarkovSemigroups/Abstract/Hypercontractivity.lean:269` | **Route A**. Plan: [`markov-semigroups/plans/gross-discharge.md`](https://github.com/mrdouglasny/markov-semigroups/blob/main/plans/gross-discharge.md). Status (2026-05-22): **ABSTRACT SPINE COMPLETE & MERGED** to ms `main` `5d09d4a` ([PR #3](https://github.com/mrdouglasny/markov-semigroups/pull/3)); pphi2 still pins the *pre-merge* ms `main`, so this row is unchanged in the pphi2 endpoint closure until the pin bump. P2 (`grossPow_hasDerivWithinAt`), P3 (`grossLogNorm_deriv_nonpos`), `grossLogNorm_antitoneOn`, the core+positive bound `eLpNorm_orbit_le_of_core_pos`, and the final general-`f` reduction `gross_lsi_implies_hypercontractive_of_hypotheses` are **all proved**; `Abstract/GrossODE.lean` is **sorry-free** (`#print axioms` = `[propext, Classical.choice, Quot.sound]`). The theorem takes four per-instance hypotheses: `CoreSemigroupInvariant`, `GeneratorCompat`, `StroockVaropoulos` (relaxed `2≤q → 1<q`, deep-think vetted), and `CoreLpL2Approx` (new 4th predicate, deep-think vetted). **Remaining endgame: merge to ms `main` → W-step** (discharge the four predicates for GaussianFin/OU — e.g. mollified-`+1/n` density for `CoreLpL2Approx`). No separate "P3 algebra / Phase 4" remains. See [`markov-semigroups/plans/gross-discharge.md`](https://github.com/mrdouglasny/markov-semigroups/blob/main/plans/gross-discharge.md) §W. |
| `ouSemigroupFin_l2_sq_hasDerivWithinAt` | `markov-semigroups` ms `c6e0e6b`: `EuclideanFin.lean:2643` | **Workstream 2.5 — ✅ DISCHARGED in ms `c0e0ce3` (2026-05-19)** but not yet propagated (pin stale). On state-(b) it disappears, replaced by the two G2 axioms below. |
| `ouSemigroupFin_preserves_IsCore` | `markov-semigroups/MarkovSemigroups/Instances/WorkInProgress/EuclideanFin.lean:2641` | **Workstream N1.b**. Per-axiom row in `markov-semigroups/AXIOM_AUDIT.md` (search `ouSemigroupFin_preserves_IsCore`). Strategy: change-of-variables on Mehler integral + `ContDiff.integral`. |
| `ouSemigroupFin_entropy_sq_decay_bound` | `markov-semigroups/MarkovSemigroups/Instances/WorkInProgress/EuclideanFin.lean:2669` | **Workstream N1.c**. Per-axiom row in `markov-semigroups/AXIOM_AUDIT.md`. Strategy: telescoping over coordinates + proved 1D `Gaussian1D.bakryEmerySpace.semigroup_entropy_sq_decay_bound`. |

**State (b) — after pin propagation** (ms `c0e0ce3`). Workstream 2.5's
discharge replaces `ouSemigroupFin_l2_sq_hasDerivWithinAt` with the two
G2 axioms. 5 inherited axioms:

| Axiom | Location | Workstream / discharge plan |
|---|---|---|
| `gross_lsi_implies_hypercontractive` | `markov-semigroups/MarkovSemigroups/Abstract/Hypercontractivity.lean:269` | **Route A** (as above). |
| `ouSemigroupFin_preserves_IsCore` | `EuclideanFin.lean:2641` | **Workstream N1.b** (as above). |
| `ouSemigroupFin_entropy_sq_decay_bound` | `EuclideanFin.lean:2669` | **Workstream N1.c** (as above). |
| `gaussianFin_diffQuot_tendsto_Lp` | `markov-semigroups/.../EuclideanGeneratorLimit.lean:183` | **Workstream G2.a** *(now on the critical path early, via the 2.5 discharge — no longer "only after Route A W-rewire")*. General Mathlib-native (operator/`fderiv`/`Measure.pi gaussianReal`), Gemini-vetted **Standard / Likely correct**. No dedicated discharge plan; ideal Mathlib upstream. |
| `gaussianFin_integrationByParts` | `markov-semigroups/.../EuclideanGeneratorLp.lean:134` | **Workstream G2.b** *(now on the critical path early, via the 2.5 discharge)*. General Mathlib-native γ-IBP fact, Gemini-vetted **Standard / Likely correct**. No dedicated discharge plan; ideal Mathlib upstream. |

**Historical note:** `polynomial_chaos_exp_moment_bridge` was the master
bridge axiom that previously dominated the closure. As of 2026-05-18
(commit `e09419a`) it is a theorem with the corrected bounded-volume
signature, and the staged follow-up `degreePiecewiseTail_layerCake_lt_top`
has now also been retired.

**After Route A's W-rewire lands** — `gross_lsi_implies_hypercontractive`
is replaced by the now-proved `gross_lsi_implies_hypercontractive_of_hypotheses`
in `Abstract/GrossODE.lean` (complete as of 2026-05-21, branch unmerged),
fed the four discharged per-instance predicates for GaussianFin/OU:
`CoreSemigroupInvariant`, `GeneratorCompat`, `StroockVaropoulos` (at the
relaxed `1 < q`), and `CoreLpL2Approx`. `GeneratorCompat` rests on the two
G2 axioms (**already on the path** via the 2.5 discharge); `CoreLpL2Approx`
is **instance-provable with no new axiom** (mollified-`+1/n` density,
deep-think vetted routine). So the W-rewire still adds only one *new* axiom
to the closure — the Stroock–Varopoulos comparison used to discharge the
`StroockVaropoulos` predicate at the instance:

| Axiom | Location | Workstream / discharge plan |
|---|---|---|
| `stroock_varopoulos` | `markov-semigroups/MarkovSemigroups/Abstract/Hypercontractivity.lean:242` | **Route A Phase 4** (per `plans/gross-discharge.md`, "discharge stroock_varopoulos itself (reuses Route B's pointwise lemma)"). |

### Honest accounting of "trio-only"

To reach `[propext, Classical.choice, Quot.sound]` only, **every**
axiom on the state-(b) path plus `stroock_varopoulos` has to close —
5 axioms: Gross (Route A), `ouSemigroupFin_preserves_IsCore` (N1.b),
`ouSemigroupFin_entropy_sq_decay_bound` (N1.c),
`gaussianFin_diffQuot_tendsto_Lp` (G2.a),
`gaussianFin_integrationByParts` (G2.b); then `stroock_varopoulos`
(Route A Phase 4) once the W-rewire lands. The 2 G2 axioms moved onto
the path **earlier than the plan originally projected** (the 2.5
discharge routes through them rather than through fresh Fubini), so
they are no longer "introduced by Route A" — they need their own
discharge work regardless of Route A timing:
- `gaussianFin_diffQuot_tendsto_Lp` (Workstream G2.a — implicit, no
  dedicated plan)
- `gaussianFin_integrationByParts` (Workstream G2.b — implicit, no
  dedicated plan)
- `stroock_varopoulos` (Route A Phase 4, planned)

The 2 G2 axioms were textbook-vetted ("Standard / Likely correct" by
Gemini); rather than rest there, both were **discharged to proved theorems**
(2026-05-22): `gaussianFin_integrationByParts` (Fubini lift of the proved 1D IBP)
and `gaussianFin_diffQuot_tendsto_Lp` (pointwise OU heat equation + L²-DCT). The
endpoint is now the bare Mathlib trio — past the "vetted textbook axioms only"
resting point.

**Workstreams not on this list:** `phase-3-smoke-test` (gaussian-hilbert,
Workstream C) is complete and contributed nothing axiomatic — the
discharge of `ouSemigroupAct_eLpNorm_hypercontractive` introduced no
new local axioms; the resulting theorem's closure is entirely composed
of the inherited markov-semigroups axioms listed above.

### Pphi2 axioms NOT on the T² OS0–OS2 critical path (off-route inventory)

For context, pphi2 has 17 active axioms total. All 17 are now off the
T² OS0–OS2 critical path and are for other constructions (S'(ℝ²) bridge, OS3 reflection positivity, OS4
mass gap, Route B' asymmetric-torus IR limit, Ward identity refinement,
Gaussian continuum-limit propagator convergence, etc.) — listed in
[`docs/AXIOM_STATUS.md`](AXIOM_STATUS.md) and [`AXIOM_AUDIT.md`](../AXIOM_AUDIT.md).
None of them are load-bearing for `torusInteracting_satisfies_OS`.

---

## Workstreams at a glance

| # | Workstream | Repo | Status | Effort remaining |
|---|---|---|---|---|
| A | Phase B Glimm–Jaffe Fourier estimates (pphi2) | pphi2 | ✅ COMPLETE 2026-05-16 | — |
| C | OU/Mehler hypercontractivity (gaussian-hilbert) | gaussian-hilbert | ✅ COMPLETE 2026-05-15; on main since 2026-05-17 | — |
| **B** | `polynomial_chaos_exp_moment_bridge` (pphi2) | pphi2 | ✅ **COMPLETE 2026-05-18** (3-step lift+narrow+rewire landed at `e09419a`; general-`P` layer-cake follow-up discharged the same day) | — |
| **2.5** | Fresh-Fubini lift for `ouSemigroupFin_l2_sq_hasDerivWithinAt` | markov-semigroups | ✅ **COMPLETE 2026-05-19** (discharged by Codex, commit `897b661`, merged via `c0e0ce3`; theorem in `EuclideanFinBE.lean` via the two G2 axioms — **not the planned fresh-Fubini route**) | — (pin propagation pending) |
| **PIN** | Propagate ms `c0e0ce3` → gaussian-hilbert → pphi2 | gh + pphi2 | not started | ~1 build cycle (pphi2 = 3896 jobs) |
| **N1.b** | `ouSemigroupFin_preserves_IsCore` | markov-semigroups | ✅ **FULLY DISCHARGED 2026-05-19** — axiom-free, sorry-free, `#print axioms`=trio, build green. Branch `discharge/n1b-preserves-iscore` `9f4beff` (Cameron–Martin + `contDiff_succ_iff_fderiv` route). **Not yet merged to ms `main` / propagated.** | — (merge + propagate pending) |
| **N1.c** | `ouSemigroupFin_entropy_sq_decay_bound` | markov-semigroups | ✅ **FULLY DISCHARGED 2026-05-19** — axiom-free, sorry-free, `#print axioms`=trio, build green (3205 jobs). Branch `discharge/n1c-entropy-decay` `bd7f950` (**also subsumes N1.b** via merge `69fc001`). Original gemini-vetted strategy had a fatal C∞ error (counterexample-confirmed); discharged via a Gemini-re-vetted **frozen-slot 1-parameter slice route** that avoids `IsCore2Fin` entirely. **Not yet merged to ms `main` / propagated.** | — (merge + propagate pending) |
| **Route A** | Abstract `gross_lsi_implies_hypercontractive` + `stroock_varopoulos` (Phase 4) | markov-semigroups | 🔄 **G2 ✅ done; P2 ✅ FULLY DISCHARGED axiom-free (`hasDerivWithinAt_integral_of_strongL2Deriv` is now a theorem, 11-lemma toolkit + ~150-line 9-step body); P3 scaffolded** (2026-05-20). Remaining: P3 algebra (~200–400 L) → W rewire (~10–30 L) → Phase 4 (`stroock_varopoulos`) | ~weeks |
| **G2.a** | Discharge `gaussianFin_diffQuot_tendsto_Lp` *(now ON the T² path early — via the 2.5 discharge, not via Route A W-rewire)* | markov-semigroups | not started; no dedicated plan; ideally upstream to Mathlib | unscoped — depends on Mathlib infrastructure availability |
| **G2.b** | Discharge `gaussianFin_integrationByParts` *(now ON the T² path early — via the 2.5 discharge)* | markov-semigroups | not started; no dedicated plan; ideally upstream to Mathlib | unscoped — depends on Mathlib infrastructure availability |

**Total parallel wall-clock to "trio + 4 inherited markov-semigroups axioms" (M1):** reached 2026-05-18 (state (a), pre-2.5 pin).
**As of 2026-05-19, all three GaussianFin BE axioms are discharged** (2.5 in ms `main`; N1.b + N1.c on branch `discharge/n1c-entropy-decay` `bd7f950`, not yet propagated). Once propagated, the T² path closure is **trio + Gross + 2 G2 axioms** — every non-Gross axiom is textbook-vetted general analysis. This is the M4b-shape resting point, reached *before* Route A even lands (2.5 routed through the G2 axioms).
**To "trio + 2 G2 textbook-vetted axioms":** blocked only on Route A (Gross) + the merge/propagation. Route A is the sole genuinely-novel remaining axiom.
**To fully trio-only (M5):** further G2.a + G2.b work, ideally as Mathlib upstreams.

Route A now **solely** dominates the critical path. As of 2026-05-20, Workstreams **B, C, 2.5, N1.b, and N1.c are all done and propagated**; **Route A's P2 analytic toolkit is also proved axiom-free** (in-measure + Vitali landed in ms `Abstract/GrossODE.lean` this session — see Route A workstream detail). The Gross axiom's analytic crux is no longer the open question; what remains is the P2 main-theorem composition (~120–150 L Mathlib plumbing) + P3 algebra + W rewire + Phase 4. Highest-ROI next action: finish the P2 main-theorem body in `Abstract/GrossODE.lean` (all inputs proved; 9-step composition plan inline + in `plans/p2-strongL2-leibniz-discharge.md`).

---

## Mathematical structure of the endpoint

```
                 ┌────────────────────────┐
                 │ Lattice GFF + e^{-V} ρ │
                 └────────────────────────┘
                              │
        (1) tightness     ┌───┴────┐  (3) Nelson exp moment bound
            of {μ_N}      │        │      uniform in (N, a)
                          ▼        ▼
              ┌──────────────────────────────┐
              │ Mitoma-Chebyshev + Prokhorov │
              │ → existence of weak limit μ∞ │
              └──────────────────────────────┘
                              │
                  (4) OS axioms transfer through weak limit
                              ▼
                ┌─────────────────────────────┐
                │ μ∞ satisfies OS0 + OS1 + OS2│
                └─────────────────────────────┘
```

All four pieces are proved end-to-end. Piece (3) was the bridge axiom
`polynomial_chaos_exp_moment_bridge`; it is a **theorem** as of
2026-05-18 (Workstream B complete, commit `e09419a`, bounded-volume
signature).

---

## Workstream-by-workstream detail

### Workstream A — Phase B Glimm–Jaffe Fourier estimates

**Repo:** pphi2 · **Status: ✅ COMPLETE 2026-05-16**

Discharges both Phase B textbook axioms in `Pphi2/NelsonEstimate/CovarianceBoundsGJ.lean`:
- `smoothWickConstant_le_log_uniform_in_aN` — was an axiom; now a theorem.
- `canonicalRoughCovariance_pow_sum_le_uniform_in_aN` — was an axiom; now a theorem.

After this, `rough_error_variance`'s closure dropped to the Mathlib trio only.

**Sub-phases (all done):**
- Phase 0: `heat_kernel_1d_bound_uniform` — `(a, N)`-uniform `C(L)·(1+1/√t)` (commit `70a484d`).
- Phase 1a: `heat_kernel_trace_bound_uniform` — tensor-product upgrade (commit `fda7ba6`).
- Phase 1b: smooth-side discharge — Schwinger + finite-sum Fubini + log-tail (commit `dc04746`).
- Phases 2–3: rough side m=1 (constant-eigenvector) + m=2 (Fubini + semigroup, exact `(2 ln 2)·T`) (commit `071ed40`).
- Phase 4: rough side m≥3 via Bochner/Minkowski + `∫_0^T s^{1/m−1} ds = m·T^{1/m}` (commit `7324738`).
- Phase 5: assembly via `by_cases` on m.

**Reference docs:**
- `docs/phase-B-textbook-axioms.md` (now marked DISCHARGED)
- `docs/phase-B-codex-handoff-2026-05-12.md` (proof-skeleton plan)
- `docs/phase-B-deep-think-record-2026-05-12.md` (Gemini deep-think verification of m=2/m≥3 routes)
- `docs/phase-B-codex-handoff-2026-05-15.md` (final integrated handoff)

---

### Workstream C — OU/Mehler hypercontractivity

**Repo:** gaussian-hilbert · **Status: ✅ COMPLETE 2026-05-15 (later)**

Discharges `ouSemigroupAct_eLpNorm_hypercontractive` (the placeholder
gaussian-hilbert axiom). gaussian-hilbert is now zero-local-axiom.

**Sub-phases (all done):**
- Phase 1 (markov-semigroups Lp-carrier abstract refactor): done before this session.
- Phase 2 (concrete `stdGaussianFin_dirichletMarkovSemigroup` bundle): markov-semigroups
  now on markov-semigroups `main` (commit `6782dc7` is preserved as `archive/feat/lp-carrier-stdGaussianFin-dirichletmarkov`).
- Phase 3 wire-in (gaussian-hilbert smoke test): commit `0f0c5eb`.
- Stage E.1: LSI bridge through bundle: commit `fbb6701`.
- Stage E.2: concrete `eLpNorm` hypercontractivity from abstract `IsHypercontractive`: commit `e1bde62`.
- Axiom retirement (delete + import refactor): commit `029156d`.

**Resulting closure** of gaussian-hilbert's `polynomial_chaos_concentration`:
standard trio + `gross_lsi_implies_hypercontractive` + 3 GaussianFin BE axioms
(all inherited from markov-semigroups).

**Reference doc:** `gaussian-hilbert/docs/hypercontractivity-discharge-plan.md`
(marked ✅ COMPLETE in the Status section).

---

### Workstream B — `polynomial_chaos_exp_moment_bridge`

**Repo:** pphi2 · **Status: 🔄 in flight (transport layer landed 2026-05-16)**

The lattice Nelson exponential moment bound — the single remaining
non-Mathlib axiom on the T² OS0–OS2 critical path.

**Statement** (`Pphi2/NelsonEstimate/PolynomialChaosBridge.lean:116`):
```
axiom polynomial_chaos_exp_moment_bridge
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ (K : ℝ), 0 < K ∧
    ∀ (a : ℝ) (ha : 0 < a), ∀ (N : ℕ) [NeZero N],
    ∫ ω, (Real.exp (-interactionFunctional d N P a mass ω)) ^ 2
        ∂(latticeGaussianMeasure d N a mass ha hmass) ≤ K
```

**6-step Glimm–Jaffe dynamical-cutoff strategy** (full plan:
`docs/polynomial-chaos-exp-moment-bridge-proof-plan.md`):

1. Covariance split `C = C_S + C_R` — ✅ done (`CovarianceSplit.lean`, `FieldDecomposition.lean`).
2. Decompose V via Wick binomial `V = V_S + E_R` — ✅ infrastructure done (`WickBinomial.lean`).
3. Smooth-side classical bound `V_S ≥ -C(1+|log T|)²` — ✅ `smooth_interaction_lower_bound_log`.
4. Rough-side polynomial-chaos concentration — ✅ all analytical inputs ready:
   - `rough_error_variance` (zero-axiom after Workstream A)
   - `polynomial_chaos_concentration` (from gaussian-hilbert after Workstream C)
5. Dynamical cutoff `T(M) := exp(−(√(M/(2C₁)) − 1))` → doubly-exp tail in `M` — ⏳ not yet wired.
6. Layer-cake integration of `∫ exp(−V)² dμ` — ⏳ scaffolding exists in `LayerCake.lean`.

**Recent infrastructure landed (chronological; all merged into pphi2 `main` 2026-05-17 via `archive/phase-b-discharge`):**

- `31df956` (2026-05-16) — transport-layer public API in `FieldDecomposition.lean`.
- `1e19b49` (2026-05-16) — Step 4 measure-transport `canonicalRoughError_neg_tail_of_stdGaussian`.
- `6ca2b1f` (2026-05-16) — Step 1/2 chaos-transport scaffolding (`finite_indexed_wick_sum_mem_wienerChaosLE`, etc.).
- `aed826d` (2026-05-17) — Step 5 + partial Step 6: `polynomial_chaos_exp_moment_bridge_quartic_bounded` for the pure-quartic bounded-volume case.
- `59c771f` (2026-05-17) — Step 6 closed: `quarticPiecewiseTail_layerCake_lt_top` discharged from axiom to theorem (small-M + large-M split with doubly-exponential decay envelope).
- `d5d274a` (2026-05-17) — **`wickPolynomial_lower_bound_general`** (WickPolynomial.lean:913): the
  quantitative general smooth-side bound `wickPolynomial P c x ≥ -A·(1 + c^(P.n/2))` for arbitrary even `P`. The single
  blocker for lifting the bridge from quartic to general `P`. Proof normalizes by `s = 1/√c`,
  proves a uniform lower bound for the compact unit-variance family `normalizedWickPolynomialPoly P s`,
  then rescales back.

**Current state of the 6 steps:**

| Step | Status |
|---|---|
| 1 — Covariance split | ✅ done |
| 2 — Wick binomial decomposition | ✅ done |
| 3 — Smooth-side classical bound | ✅ done **(now general in `P` via `wickPolynomial_lower_bound_general`)** |
| 4 — Rough-side polynomial-chaos concentration | ✅ general in `P` at `RoughErrorBound.lean:3655` |
| 5 — Dynamical cutoff `T(M)` | ✅ done (via `polynomial_chaos_exp_moment_bridge_quartic_bounded`) |
| 6 — Layer-cake integration | ✅ done (`quarticPiecewiseTail_layerCake_lt_top` is a theorem) |
| **Master bridge** | 🔄 still an axiom; **the original `∀ a > 0` statement is mathematically false** without a volume constraint — needs a narrowing refactor + lift from quartic to general `P` |

**Pphi2 active axiom count:** 17 (back from the temporary 18 after the staging axiom discharge).

**Critical design decision: the master axiom statement is over-strong.** The proof
plan (`docs/polynomial-chaos-exp-moment-bridge-proof-plan.md`:282) flags that
`∃ K, ∀ a > 0, ∀ N, …` is **false** without a volume constraint — the
`interactionFunctional_bounded_below` witness scales like `a^d · |Λ|`, not uniformly in N.
The original `∀ a > 0` shape was a "downstream-consumer convenience" that turned out
to be unprovable.

**Consumer audit (verified 2026-05-17):** both consumers
(`nelson_exponential_estimate_lattice` in NelsonEstimate.lean:81 and
`asymNelson_exponential_estimate` in AsymTorusInteractingLimit.lean:69) already
operate at fixed `L = N·a` (via `circleSpacing L N = L/N` and `asymGeomSpacing Lt Ls N`
respectively). They pass **general `P`** through, but always at bounded volume. So the
refactor is invisible to downstream callers.

**Next concrete steps:**

1. **Lift `polynomial_chaos_exp_moment_bridge_quartic_bounded` to general even `P`**:
   thread `m := P.n` through `canonicalRoughError_neg_tail_of_stdGaussian` and use
   the new `wickPolynomial_lower_bound_general` for the smooth cutoff threshold
   `T(M)` (degree-dependent: `s = P.n / 2` instead of hardcoded `s = 2`).
2. **Narrow the master axiom** to require `_hvol : (N:ℝ)*a = L` (replacing the false
   `∀ a > 0` with the honest bounded-volume statement). The lifted general-`P`
   theorem discharges it directly.
3. **Rewire consumers** (mechanical — both already supply `circleSpacing_volume_eq` /
   `asymGeomSpacing_volume_eq` as one-liners).

After (1)+(2)+(3): `polynomial_chaos_exp_moment_bridge` becomes a theorem with its
(corrected) bounded-volume signature; pphi2 active axiom count drops **17 → 16**;
`#print axioms torusInteracting_satisfies_OS` no longer cites it (modulo the
branch-chain merge).

**Estimated remaining:** ~150–300 lines / ~1 week.

---

### Workstream 2.5 — `ouSemigroupFin_l2_sq_hasDerivWithinAt`

**Repo:** markov-semigroups · **Status: ✅ COMPLETE 2026-05-19**

`ouSemigroupFin_l2_sq_hasDerivWithinAt` is now a **theorem** in
`MarkovSemigroups/Instances/WorkInProgress/EuclideanFinBE.lean:446`
(discharged by Codex, commit `897b661`, merged into markov-semigroups
`main` via `c0e0ce3`). The axiom is removed from `EuclideanFin.lean`.

**Route actually taken — not the planned fresh-Fubini lift.** Instead of
the dual-vetted Fubini-through-`ouSemigroupFin_insertNth_eq` plan, the
discharge identifies `∫ (P_s f)² dγ_n` with the L² pairing
`⟪[f], P_{2s}[f]⟫`, differentiates the pairing via the strong-L²
difference-quotient theorem, then converts the derivative to
`−2·E(P_t f, P_t f)` via the multivariate Gaussian integration-by-parts
identity.

**Closure consequence — shape change, not a shrink.** The discharged
theorem's verified closure is
`[propext, Classical.choice, Quot.sound, gaussianFin_diffQuot_tendsto_Lp,
gaussianFin_integrationByParts, ouSemigroupFin_preserves_IsCore]`. So
2.5 trades `ouSemigroupFin_l2_sq_hasDerivWithinAt` for the two G2 axioms
(`gaussianFin_diffQuot_tendsto_Lp`, `gaussianFin_integrationByParts`) —
both Gemini-vetted "Standard / Likely correct" general Mathlib-native
facts. This is the M4a-style shape change arriving early (see
"Milestones"). N1.b's `ouSemigroupFin_preserves_IsCore` also appears in
this closure (it always did, as a dependency).

**Remaining to realize it in pphi2:** propagate the pin chain (Workstream
**PIN** in the table) — gaussian-hilbert and pphi2 still pin ms at the
pre-2.5 `c6e0e6b`.

---

### Workstream N1.b — `ouSemigroupFin_preserves_IsCore`

**Repo:** markov-semigroups · **Status: ✅ FULLY DISCHARGED 2026-05-19**
(branch `discharge/n1b-preserves-iscore`, commit `9f4beff`; not yet
merged to ms `main` / propagated)

`ouSemigroupFin_preserves_IsCore` is now an axiom-free, sorry-free
`theorem`; `#print axioms` = `[propext, Classical.choice, Quot.sound]`;
full build green (3203 jobs). ms GaussianFin axiom count 11 → 10
(AXIOM_AUDIT/status/README updated on the branch).

**Route taken** (Gemini-deep-think-refined Cameron–Martin route, *not* the
originally-planned explicit-density `ContDiff.integral`): Cameron–Martin
weight keeping the γ measure + `contDiff_succ_iff_fderiv` strong
induction (deliberately avoids `iteratedFDeriv`). Chain: `cameronMartin1D`
→ `gaussianFin_cameronMartin` (tensorize by induction on `n` via
`integral_γFin_succAbove`) → `ouSemigroupFin_eq_cmKernel` →
`contDiff_laplaceFamily` → `contDiff_ouSemigroupFin_of_bounded`. See
[[ms-cameron-martin-contdiff-route]] (project memory) for the reusable
technique + Mathlib API discoveries.

---

### Workstream N1.c — `ouSemigroupFin_entropy_sq_decay_bound`

**Repo:** markov-semigroups · **Status: ✅ FULLY DISCHARGED 2026-05-19**
(branch `discharge/n1c-entropy-decay`, commit `bd7f950`; this branch
**also subsumes N1.b** via merge `69fc001`; not yet merged to ms
`main` / propagated)

`ouSemigroupFin_entropy_sq_decay_bound` is now an axiom-free,
sorry-free `theorem`; `#print axioms` = `[propext, Classical.choice,
Quot.sound]` (verified after a full clean build — `lake env lean`
alone can spuriously report `sorryAx` from a stale `.olean`); full
build green (3205 jobs). `EuclideanFin.lean` has 0 axioms, 0 sorries.

**The originally gemini-3.1-pro-vetted (2026-05-13) "telescoping over
coordinates + proved 1D" strategy contained a fatal mathematical
error** (discovered 2026-05-19, independently re-vetted wrong by Gemini
deep-think + 3.1-pro): it assumed the single-coordinate Mehler
telescope iterates `ouCoord j t g` stay C∞. They do not — single-coord
Mehler smooths only the *integrated* coordinate, so under `IsCoreFin`
(pure ≤2nd-order bounds) the iterate is generically only C² jointly
(3rd passthrough derivative diverges for `t > ½ ln 2`; explicit
counterexample). See [[ms-n1c-telescoping-c2-finding]] (project memory).

**Route actually taken** (Gemini-re-vetted before implementing —
lower-risk than even the corrected S1–S5 C²-route, which it
superseded): **no `IsCore2Fin` predicate at all**. Refactor the
per-coordinate step lemma to slice-level hypotheses with an *abstract
slice-derivative*; exploit the **frozen-slot decoupling** — for
`k∉S`, `setShift S t (update x k r) y = update (setShift S t x y) k r`,
so the `k`-slice of `ouCoordSet S t g` is a *1-parameter* γ-average of
`g`'s `k`-slices — never needing mixed partials or joint C². Single
real-parameter differentiation under the γ-integral via Mathlib
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` with a *constant*
dominator (γₙ is a probability measure). Pointwise kernel
Cauchy–Schwarz (`cauchy_schwarz_measure`) + `integral_ouCoordSet_eq`
give orthogonal Fisher monotonicity; `Finset.induction` telescope +
ε→0 DCT tail close it. The salvaged axiom-free T1 factorization layer
(9 lemmas: `ouCoord`, `ouCoordSet`, `ouCoord_ouCoordSet`,
`integral_ouCoordSet_eq`, …) was reused.

---

### Route A — Abstract `gross_lsi_implies_hypercontractive`

**Repo:** markov-semigroups · **Status: 🔄 in flight (2026-05-20: G2 ✅ done; P2 analytic toolkit ✅ proved axiom-free; P3 scaffolded)**
**Effort remaining: ~weeks.** Per `plans/gross-discharge.md` and `plans/p2-strongL2-leibniz-discharge.md` (2026-05-20):
* **P2 analytic toolkit ✅** — 11-lemma proof toolkit in `Abstract/GrossODE.lean` covering FTC factoring, `averagedDerivField` def + factorization + a.e./pointwise sub bounds + measurability + MemLp, the user's UI helper, **in-measure convergence** (`averagedDerivField_tendstoInMeasure`), **Vitali L²-convergence** (`averagedDerivField_tendsto_eLpNorm`), and the target `MemLp(ψ' ∘ u_s)`. The lemma statement was Gemini-counterexample false originally; patched to the corrected `h_u_bound`-orbit form. Main theorem body is a documented `sorry` with a 9-step composition plan (~120–150 L Mathlib-API plumbing remain: Lp lifting, `Filter.Tendsto.inner`, integrated factorization, `hasDerivWithinAt_iff_tendsto_slope` close).
* Remaining `hasDerivAt_integral_rpow_exponent` DCT plumbing + `grossPow_*`/glue ⬜.
* P3 algebra (`grossLogNorm_deriv_nonpos` + interior-continuity bridge + final `eLpNorm ↔ ∫·^q` reduction, ~200–400 L) ⬜.
* W rewire (~10–30 L) ⬜.
* Phase 4 (`stroock_varopoulos`) ⬜.

Discharges the abstract Gross 1975 theorem at
`MarkovSemigroups/Abstract/Hypercontractivity.lean:269`. The "headline"
axiom — the one Mathlib doesn't have.

**Primary plan doc:** [`markov-semigroups/plans/gross-discharge.md`](https://github.com/mrdouglasny/markov-semigroups/blob/main/plans/gross-discharge.md)
(lives on markov-semigroups `main` via commits `ef272f6` and `6dc2026`).

**Plans index:** [`markov-semigroups/plans/README.md`](https://github.com/mrdouglasny/markov-semigroups/blob/main/plans/README.md)
catalogues both Route A and the superseded Route B alternative.

**G2 + scaffolding landed 2026-05-17** (now on markov-semigroups `main` since 2026-05-17; merge tip `aa9cc47` preserved as `archive/feat/lp-carrier-stdGaussianFin-dirichletmarkov`):

- `GaussianFin.generatorCompat_stdGaussianFin` is **sorry-free**.
  `#print axioms` = standard trio + exactly two custom axioms:
  `gaussianFin_diffQuot_tendsto_Lp` and `gaussianFin_integrationByParts`
  — both *general, Mathlib-native* (no project defs;
  operator/`fderiv`/`Measure.pi gaussianReal`), Gemini-vetted
  **Standard / Likely correct**.
- A third Gross-discharge axiom `gaussianOU_heatEquation_within_zero`
  (also Standard-vetted) was subsumed by the DCT axiom and is **off**
  `generatorCompat`'s live critical path (retained as reusable
  textbook infrastructure).
- These discharged the deep `EuclideanGenerator{Lp,Limit}` cruxes
  (heat equation, γ-IBP, DCT) that previous attempts stalled on.
- The prior `ouGeneratorFin_ibp` Lp-coercion bridge is also closed.

**Abstract Gross relocated + P2/P3 scaffolded:**

- `gross_lsi_implies_hypercontractive_of_hypotheses` moved out of
  `Abstract/Hypercontractivity.lean` (the `CoreSemigroupInvariant` /
  `GeneratorCompat` / `StroockVaropoulos` predicates stay there) into
  a new `Abstract/GrossODE.lean`.
- The legacy `gross_lsi_implies_hypercontractive` axiom is retained
  (non-breaking; gaussian-hilbert keeps compiling) until P2/P3 close
  and the call-site is rewired (the **W** workstream step).
- In `GrossODE.lean`: the exponent-path calculus (`grossExponent`,
  `hasDerivAt_grossExponent` = the `q'=2ρ(q-1)` coupling), the
  **P2 chain-rule assembly** (`grossLogNorm_hasDerivWithinAt` from
  F'/Ent via `field_simp;ring`), the **P3 `antitoneOn` closure**
  (`antitoneOn_of_hasDerivWithinAt_nonpos` on `Set.Ici 0`), and the
  elementary `hasDerivAt_abs_rpow_exponent` are all **proved**.
- The P2 bottleneck is decomposed (no axiom — that would be circular)
  into a general Mathlib-native exponent-path Leibniz lemma (its
  pointwise core proved) and a general Mathlib-native Bochner–Leibniz
  lemma through a strong-`L²` derivative (the reusable kernel, *to be
  proved*, not axiomatized).

**Current markov-semigroups axiom / sorry inventory** (on the active
feature branch, per `markov-semigroups/status.md` 2026-05-17 entry;
`AXIOM_AUDIT.md` is canonical for the registered set):

- **19 declared `.lean` axioms**: the 3 Gross-discharge general axioms
  above, 3 `EuclideanFin` BE tensor-lift axioms (Phase 2.5 / N1.b /
  N1.c targets), 4 `EuclideanTests` scratch axioms, the legacy abstract
  Gross/S-V trio (legacy until rewire), Dobrushin–Zegarliński,
  Schwartz-convolution, diamagnetic.
- **9 sorries**: 8 in `Abstract/GrossODE.lean` (documented P2/P3 work
  items — `grossPow_pos`, `grossEntropy_eq`, the two general Leibniz
  lemmas, the `grossPow_hasDerivWithinAt` glue, `grossLogNorm_deriv_nonpos`
  P3 algebra, the `antitoneOn` continuity bridge, and the final
  `eLpNorm↔∫·^q` reduction) + 1 in `TwoPoint.lean` (quarantined,
  mathematically false for jump processes).

**Remaining Gross endgame:** P2 (the one general Leibniz kernel + thin
glue) → P3 algebra → W (call-site rewire).

**Why Route A, not Route B (concrete Gaussian1D):** the live pphi2 chain
consumes the abstract axiom (via gaussian-hilbert
`HypercontractivityFromBE.lean:204`), not a concrete Gaussian1D instance.
Discharging the abstract axiom directly makes pphi2 Gross-axiom-free
with zero re-plumbing of gaussian-hilbert.

**Phases:**
- **Phase 0 (the crux):** `DirichletMarkovSemigroup` is structurally too thin —
  no core-invariance under `P_t`, only a t=0⁺ form. Add `IsCore_semigroup`;
  bootstrap the all-t generator–form identity from the semigroup law +
  `energy_eq_deriv` (no generator field needed). **Breaking structure change.
  Vet with deep-think/Codex before touching.**
- **Phase 1:** bootstrap identity.
- **Phase 2:** eLpNorm / parametric-derivative machinery (~800–1500-line bottleneck).
- **Phase 3:** algebraic closure (trivially closes via existing `stroock_varopoulos`
  axiom + LSI + `q' = 2ρ(q-1)`).
- **Phase 4:** discharge `stroock_varopoulos` itself (reuses Route B's
  pointwise lemma).

**Interaction with other workstreams:**
- **Workstream B (pphi2):** mathematically independent. Route A's
  structural change to `DirichletMarkovSemigroup` flows transitively
  through gaussian-hilbert to pphi2, but doesn't change the mathematics.
- **Phase 2.5 / N1.b / N1.c:** Phase 0's new `IsCore_semigroup` field on
  `DirichletMarkovSemigroup` requires the Phase 2 bundle to add that
  field. Either (a) Route A's Phase 0 lands first and the others rebase
  on it, or (b) the others land first and Route A includes a
  bundle-field migration step.

**Superseded plan:** [`markov-semigroups/plans/gaussian-ou-hypercontractivity.md`](https://github.com/mrdouglasny/markov-semigroups/blob/main/plans/gaussian-ou-hypercontractivity.md)
is now flagged SUPERSEDED — its strategic premise that abstract Gross axioms
are not used was false in the as-built code. Retained for its reusable
Stroock–Varopoulos / Mehler-kernel techniques.

---

## Dependency / coordination map

```
pphi2 (Workstreams A+B done; pins gh@2df8345, ms@c6e0e6b — PRE-2.5, STALE)
   ↓ imports
gaussian-hilbert (zero local axioms; Workstream C done; pins ms@c6e0e6b — PRE-2.5, STALE)
   ↓ imports
markov-semigroups main@c0e0ce3 (2.5 ✅ done; N1.b + N1.c + Route A live here)
```

**File-level conflict matrix:**

|  | Workstream B | Phase 2.5 | N1.b | N1.c | Route A |
|---|---|---|---|---|---|
| pphi2/NelsonEstimate/PolynomialChaosBridge.lean | ✏️ | | | | |
| pphi2/NelsonEstimate/FieldDecomposition.lean | ✏️ | | | | |
| ms/Abstract/Hypercontractivity.lean | | | | | ✏️ (structure) |
| ms/Instances/WIP/EuclideanFin.lean:2643 | | ✏️ | | | |
| ms/Instances/WIP/EuclideanFin.lean:2771 | | | ✏️ | | |
| ms/Instances/WIP/EuclideanFin.lean:2799 | | | | ✏️ | |
| ms/Instances/WIP/EuclideanFinLp.lean (Phase 2 bundle) | | ✏️ (delegate to fresh-Fubini) | | | ✏️ (add field) |

The bundle file `EuclideanFinLp.lean` is the only multi-touched file: Phase 2.5
modifies the `energy_eq_deriv` proof to use the new fresh-Fubini theorem,
and Route A's Phase 0 adds the `IsCore_semigroup` field. **These two
should be co-staged** if running concurrently.

---

## Recommended sequencing

**Done:** Workstreams A, B, C, **2.5, N1.b, N1.c** all complete. N1.b +
N1.c are both on branch `discharge/n1c-entropy-decay` `bd7f950`
(N1.c's branch subsumes N1.b via merge `69fc001`), axiom-free, build
green, **not yet merged to ms `main` / propagated**. Remaining: the
branch merge + pin propagation, Route A, and the off-route G2.a/G2.b.

**Immediate:**

1. **Merge + propagate** — merge `discharge/n1c-entropy-decay`
   (subsumes N1.b) into ms `main`; verify `#print axioms` of both
   theorems = trio on `main` after a full `lake build` (the `.olean`
   staleness caveat: `lake env lean` alone can spuriously report
   `sorryAx`); gaussian-hilbert bumps ms pin → new HEAD, rebuild;
   pphi2 bumps gh+ms pins, rebuild (3896 jobs), re-verify
   `#print axioms torusInteracting_satisfies_OS`. This makes
   2.5 + N1.b + N1.c all real in the pphi2 endpoint at once →
   closure becomes trio + Gross + 2 G2 axioms.
2. **Route A** — the sole remaining long pole; P2 kernel + P3 algebra
   + W + Phase 4.

**Note:** N1.b and N1.c both live in `EuclideanFin.lean` (post-`c0e0ce3`
refactor); they were developed in separate worktrees and the N1.c
branch already merged N1.b in cleanly at `69fc001` (zero conflicts —
disjoint declaration blocks), so the eventual ms-`main` merge is N1.c's
branch (which subsumes N1.b).

**Route A:** vet the Phase 0 design with Gemini deep-think + Codex *before* touching the
`DirichletMarkovSemigroup` structure. The other agent flagged this as the
"one mistake that wastes the whole effort." After vetting, decide whether
to launch a dedicated Route A campaign (multi-week) or accept Gross as the
final inherited textbook axiom.

---

## Milestones

(See "Complete axiom-and-sorry inventory" section above for the
per-axiom accounting.)

- **M1 — ✅ REACHED 2026-05-18 (state (a)):** Workstream B landed.
  pphi2 has **zero local axioms on the T² critical path**. Endpoint
  closure is the standard trio + 4 inherited markov-semigroups axioms
  (Gross + 3 GaussianFin BE tensor-lifts). Defensible mathematical
  resting point. *(Still the live closure on pphi2 `main` until pin
  propagation.)*
- **M2 — ✅ ACHIEVED in markov-semigroups 2026-05-19; pending pin
  propagation to be visible in pphi2.** Workstream 2.5 landed. It does
  **not** drop an axiom — it **changes the closure shape**: trades
  `ouSemigroupFin_l2_sq_hasDerivWithinAt` for the two G2 axioms
  (`gaussianFin_diffQuot_tendsto_Lp`, `gaussianFin_integrationByParts`).
  Post-propagation closure (state (b)): trio + Gross + N1.b + N1.c + 2
  G2 = 5 inherited axioms. *(The original M2 prediction "one inherited
  axiom drops → trio + 3" was wrong; the discharge routes through the
  G2 axioms, not fresh Fubini. This is the M4a-style shape change
  arriving early.)*
- **M3 — ✅ ACHIEVED in markov-semigroups 2026-05-19; pending branch
  merge + pin propagation to be visible in pphi2.** N1.b and N1.c are
  both fully discharged (axiom-free, build green) on branch
  `discharge/n1c-entropy-decay` `bd7f950`. Post-propagation closure:
  **trio + `gross_lsi_implies_hypercontractive` + 2 G2 axioms.** All
  three GaussianFin BE axioms are now theorems; the only genuinely-novel
  remaining axiom on the T² path is Gross. *(N1.c's original
  gemini-vetted strategy had a fatal C∞ error — see the N1.c
  workstream detail; it was rescued via a re-vetted frozen-slot
  1-parameter route.)*
- **M4a (multi-week from M3):** Route A's P2 + P3 + W rewire lands.
  `gross_lsi_implies_hypercontractive` is replaced by the proved
  `gross_lsi_implies_hypercontractive_of_hypotheses`. The 2 G2 axioms
  are **already on the path** (via 2.5), so the W-rewire now adds only
  **one** new axiom (`stroock_varopoulos`), not three. Closure: trio +
  2 G2 + `stroock_varopoulos`.
- **M4b (a few days from M4a):** Route A Phase 4 lands.
  `stroock_varopoulos` discharged via Route B's pointwise lemma.
  Closure: trio + 2 G2 axioms (`gaussianFin_diffQuot_tendsto_Lp`,
  `gaussianFin_integrationByParts`). This is the **honest "trio +
  textbook-vetted" resting point** — every remaining axiom is a
  general analysis fact that wants to be in Mathlib.
- **M5 (further work, no dedicated plans yet):** Discharge the 2
  G2 axioms (Workstreams G2.a, G2.b). Both are general
  Mathlib-native; the long-term path is to upstream them to Mathlib
  rather than maintain in-project. Closure: **standard Mathlib trio
  only**. This is the project's ultimate axiom-free milestone.

---

## Reference docs

**Per-workstream plans (in this repo unless noted):**

| Workstream | Plan doc(s) |
|---|---|
| A | [`docs/phase-B-textbook-axioms.md`](phase-B-textbook-axioms.md), [`docs/phase-B-codex-handoff-2026-05-12.md`](phase-B-codex-handoff-2026-05-12.md), [`docs/phase-B-codex-handoff-2026-05-15.md`](phase-B-codex-handoff-2026-05-15.md), [`docs/phase-B-deep-think-record-2026-05-12.md`](phase-B-deep-think-record-2026-05-12.md) |
| B | [`docs/polynomial-chaos-exp-moment-bridge-proof-plan.md`](polynomial-chaos-exp-moment-bridge-proof-plan.md), [`docs/rough-error-variance-plan.md`](rough-error-variance-plan.md) (Step 1 sub-plan, marked COMPLETED) |
| C | [`gaussian-hilbert/docs/hypercontractivity-discharge-plan.md`](https://github.com/mrdouglasny/gaussian-hilbert/blob/main/docs/hypercontractivity-discharge-plan.md) |
| 2.5 | discharge plan inline at `markov-semigroups/MarkovSemigroups/Instances/WorkInProgress/EuclideanFin.lean:2637-2641` (dual-vetted, gemini-2.5-pro + gemini-3.1-pro 2026-05-13) |
| N1.b | per-axiom row in [`markov-semigroups/AXIOM_AUDIT.md`](https://github.com/mrdouglasny/markov-semigroups/blob/main/AXIOM_AUDIT.md) (search `ouSemigroupFin_preserves_IsCore`) |
| N1.c | per-axiom row in [`markov-semigroups/AXIOM_AUDIT.md`](https://github.com/mrdouglasny/markov-semigroups/blob/main/AXIOM_AUDIT.md) (search `ouSemigroupFin_entropy_sq_decay_bound`) |
| Route A | [`markov-semigroups/plans/gross-discharge.md`](https://github.com/mrdouglasny/markov-semigroups/blob/main/plans/gross-discharge.md) (new, by another agent); index at [`markov-semigroups/plans/README.md`](https://github.com/mrdouglasny/markov-semigroups/blob/main/plans/README.md) |

**Status snapshots:**
- `docs/T2-continuum-limit-status-2026-05-13.md` — earlier comprehensive snapshot
- `docs/AXIOM_STATUS.md` — pphi2 axiom inventory
- `AXIOM_AUDIT.md` — pphi2 per-axiom audit log
- `gaussian-hilbert/STATUS.md`, `gaussian-hilbert/AXIOM_AUDIT.md`
- `markov-semigroups/status.md`, `markov-semigroups/AXIOM_AUDIT.md`

**Per-commit log of this campaign:** the prior `phase-b-discharge` history is preserved as the `archive/phase-b-discharge` tag; `git log archive/phase-b-discharge` (or browsing the merge commit `b0ebee3` on main) shows the full per-commit trail.
