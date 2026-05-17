# T² φ⁴₂ continuum limit — master plan & progress tracker

**Last refreshed:** 2026-05-16
**Repo:** pphi2 (this) + sister repos gaussian-hilbert, markov-semigroups
**Endpoint:** `Pphi2.torusInteracting_satisfies_OS` (OS0 + OS1 + OS2 for the T²_L
symmetric-torus φ⁴₂ continuum limit)
**Branch:** `phase-b-discharge` (current working branch; not yet merged to main)

This document is the **single source of truth** for the T² OS0–OS2 endpoint
campaign. It tracks the five workstreams that, when complete, reduce the
endpoint's axiom closure to `[propext, Classical.choice, Quot.sound]`
only. Per-workstream details and proof plans live in their dedicated docs
(linked from each row below).

---

## Current closure

`#print axioms Pphi2.torusInteracting_satisfies_OS` (verified 2026-05-16):
```
[propext, Classical.choice, Quot.sound, polynomial_chaos_exp_moment_bridge]
```

After Workstream B lands, the closure transitively surfaces 4 markov-semigroups
axioms (`gross_lsi_implies_hypercontractive` + 3 GaussianFin BE axioms).
After Workstreams 2.5 + N1.b + N1.c + Route A all land, the closure becomes
the Mathlib trio only.

> ⚠️ The closure surface above is **conditional on a pin-chain merge** —
> see "Branch chain & pin state" below.

---

## ⚠️ Branch chain & pin state (CRITICAL — audit-as-of 2026-05-16)

This session's work is spread across **feature branches in all three repos**.
pphi2's pins still point at each upstream's `main`, which **predates the
Workstream C and markov-semigroups Phase 2 work**. The current
`#print axioms` only shows `[trio + polynomial_chaos_exp_moment_bridge]`
because the bridge is still an axiom — opaque, so its (would-be)
transitive dependencies don't surface. When Workstream B converts the
bridge to a theorem, the closure will reflect **the pinned upstream**,
not the as-built feature-branch state.

| Repo | Active branch | Has the new work? | pphi2's current pin | Pin currency |
|---|---|---|---|---|
| **pphi2** | `phase-b-discharge` | ✅ Workstream A + B-transport + master plan | — (self) | — |
| **gaussian-hilbert** | `phase-3-smoke-test` | ✅ Workstream C (E.1, E.2, axiom retirement, doc refresh) | `main` (`75123d02`) | **pre-Workstream-C** |
| **markov-semigroups** | `feat/lp-carrier-stdGaussianFin-dirichletmarkov` | ✅ Phase 2 bundle | `main` (`1bfe3868`), inherited via gaussian-hilbert | **pre-Phase-2** |

### Why the build still works

The bridge axiom `polynomial_chaos_exp_moment_bridge` is opaque, so
`#print axioms` doesn't (yet) see the gaussian-hilbert /
markov-semigroups chain. Once Workstream B discharges the bridge,
`#print axioms` will surface whatever's behind it — and against the
**current** pphi2 pins, that surface includes
`ouSemigroupAct_eLpNorm_hypercontractive` as an axiom (pre-Workstream-C
state in gaussian-hilbert main), **not** the post-discharge closure
we've been planning around.

### Required merge order (do this before Workstream B's final
`#print axioms` verification)

1. **markov-semigroups**: merge `feat/lp-carrier-stdGaussianFin-dirichletmarkov`
   → main. 2 commits ahead of main (`6782dc7`, `2e9121f`). PR-ready,
   builds clean.
2. **gaussian-hilbert**: merge `phase-3-smoke-test` → main. 6 commits
   ahead of main (`0f0c5eb`, `a1fc35e`, `fbb6701`, `e1bde62`, `029156d`,
   `3a789d5`). PR-ready, builds clean. Includes a pin bump to the now-current
   markov-semigroups main from step 1.
3. **pphi2**: `lake update` to bump both gaussian-hilbert and
   markov-semigroups pins to their new mains. Confirm `lake build` clean.
   Then merge `phase-b-discharge` → main (after Workstream B finishes).

After these three merges, pphi2 main consumes the actually-discharged
gaussian-hilbert + markov-semigroups Phase 2 state. Workstream B's
final axiom-closure verification will then produce the planned
"`[trio + 4 inherited markov-semigroups axioms]`" closure.

### Workstream B is **not blocked** by this

Workstream B can continue development on `phase-b-discharge` against the
current pins. Only the **final axiom-closure check** at end-of-Workstream-B
needs the pin bumps to have happened — and we can do step 1 and step 2 of
the merge order in parallel with Workstream B's development. **Recommended:
land steps 1 + 2 now** so they're not in the way when Workstream B finishes.

### Tracking sister-repo branch state

A quick three-line audit:
```sh
git -C /Users/mdouglas/Documents/GitHub/pphi2          log origin/main..phase-b-discharge --oneline | wc -l
git -C /Users/mdouglas/Documents/GitHub/gaussian-hilbert log origin/main..phase-3-smoke-test --oneline | wc -l
git -C /tmp/markov-semigroups-phase2 log origin/main..feat/lp-carrier-stdGaussianFin-dirichletmarkov --oneline | wc -l
```
shows how many commits each branch is ahead of its main; "0" means the
chain is fully merged.

---

## Workstreams at a glance

| # | Workstream | Repo | Status | Effort remaining |
|---|---|---|---|---|
| A | Phase B Glimm–Jaffe Fourier estimates (pphi2) | pphi2 | ✅ COMPLETE 2026-05-16 | — |
| C | OU/Mehler hypercontractivity (gaussian-hilbert) | gaussian-hilbert | ✅ COMPLETE 2026-05-15 | — |
| **B** | `polynomial_chaos_exp_moment_bridge` (pphi2) | pphi2 | 🔄 in flight | ~1–2 wk |
| **2.5** | Fresh-Fubini lift for `ouSemigroupFin_l2_sq_hasDerivWithinAt` | markov-semigroups | not started | ~1.5 days |
| **N1.b** | `ouSemigroupFin_preserves_IsCore` | markov-semigroups | not started | ~3–5 days |
| **N1.c** | `ouSemigroupFin_entropy_sq_decay_bound` | markov-semigroups | not started | ~3–5 days |
| **Route A** | Abstract `gross_lsi_implies_hypercontractive` | markov-semigroups | not started (plan drafted) | multi-week, structural |

**Total parallel wall-clock to fully zero-local-axiom T² endpoint:** ~3–5 weeks
if all five run in parallel; ~6–10 weeks serial. Route A dominates the
critical path.

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

Pieces (1), (2), (4) are proved end-to-end. Piece (3) is the bridge axiom
`polynomial_chaos_exp_moment_bridge` (Workstream B target).

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
  `feat/lp-carrier-stdGaussianFin-dirichletmarkov`, commit `6782dc7`.
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

**Recent infrastructure landed (chronological, all on `phase-b-discharge`):**

- `31df956` (2026-05-16) — transport-layer public API in `FieldDecomposition.lean`
  (additivity, smul, pointwise measurability, `canonicalSumConfig`, `memLp_two` lemmas).
- `1e19b49` (2026-05-16) — Step 4 measure-transport: `canonicalRoughError_neg_tail_of_stdGaussian`
  (RoughErrorBound.lean:442), composing `canonicalJointMeasure_map_stdGaussian` +
  `chaos_neg_tail_bound`.
- `6ca2b1f` (2026-05-16) — Step 1/2 chaos-transport scaffolding:
  `finite_indexed_wick_sum_mem_wienerChaosLE`, `canonicalStdIndex` family,
  `canonicalJointMultiIndexOfPair` + total-degree + Wick-product lemmas, plus
  inverse-coordinate lemmas for `canonicalJointStdGaussianMeasurableEquiv.symm`.
- `aed826d` (2026-05-17) — Step 5 + partial Step 6:
  `polynomial_chaos_exp_moment_bridge_quartic_bounded` (PolynomialChaosBridge.lean:399)
  composes the smooth cutoff bound + rough cutoff tail automatically for the
  pure-quartic, bounded-volume case. Step 6 (layer-cake) gap isolated as a
  single staging axiom `quarticPiecewiseTail_layerCake_lt_top` — a pure
  integrability fact (finiteness of the layer-cake integral under the
  derived doubly-exponential tail).

**Current state of the 6 steps:**

| Step | Status |
|---|---|
| 1 — Covariance split | ✅ done |
| 2 — Wick binomial decomposition | ✅ done |
| 3 — Smooth-side classical bound | ✅ done |
| 4 — Rough-side polynomial-chaos concentration | ✅ measure-transport + scaffolding done; representative + chaos-membership work in flight |
| 5 — Dynamical cutoff `T(M)` | ✅ done (via `polynomial_chaos_exp_moment_bridge_quartic_bounded`) |
| 6 — Layer-cake integration | 🟡 gap isolated as staging axiom `quarticPiecewiseTail_layerCake_lt_top` |
| **Master bridge** | 🔄 still an axiom; quartic-bounded specialisation is a theorem |

**Pphi2 active axiom count:** 17 → 18 (the new staging axiom `quarticPiecewiseTail_layerCake_lt_top` is in PolynomialChaosBridge.lean).

**Next concrete steps:**
1. Discharge `quarticPiecewiseTail_layerCake_lt_top` (pure integrability;
   doubly-exp tail dominates `exp(2M)` so `∫₀^∞ ... dM < ∞` is elementary
   Lebesgue-integral bookkeeping). Pphi2 axiom count then drops back to 17.
2. Use `polynomial_chaos_exp_moment_bridge_quartic_bounded` to push the
   quartic bounded-volume case upward toward the master bridge
   `polynomial_chaos_exp_moment_bridge`.
3. After (2): pphi2 has **zero non-Mathlib axioms** on the T² critical
   path; inherited markov-semigroups axioms then surface in the
   `#print axioms` closure (subject to the branch-chain merge documented above).

**Estimated remaining:** ~200–400 lines / 1 week.

---

### Workstream 2.5 — Fresh-Fubini for `ouSemigroupFin_l2_sq_hasDerivWithinAt`

**Repo:** markov-semigroups · **Status: not started (dual-vetted plan in place)**
**Effort: ~1.5 active days.**

Replaces the polarization-based proof of `energy_eq_deriv` in the Phase 2
bundle with the fresh-Fubini lift of the discharged 1D theorem
`Gaussian1D.bakryEmerySpace.semigroup_l2_sq_hasDerivWithinAt`. This
discharges `ouSemigroupFin_l2_sq_hasDerivWithinAt` in
`MarkovSemigroups/Instances/WorkInProgress/EuclideanFin.lean:2643`.

**Strategy** (per the discharge plan documented inline at EuclideanFin.lean:2637-2641,
dual-vetted by gemini-2.5-pro + gemini-3.1-pro on 2026-05-13):
- Fubini lift through `ouSemigroupFin_insertNth_eq` and `integral_γFin_succAbove`.
- Differentiate per-coordinate via the proved 1D fact.
- Recombine by linearity of derivative.
- Use dominated convergence to justify swap of `∂/∫`.

**Side effects:** drops markov-semigroups' GaussianFin axiom count 11 → 10
and removes one of the 4 inherited axioms from the T² closure.

**Why now:** smallest, well-vetted plan, biggest impact-per-effort.

---

### Workstream N1.b — `ouSemigroupFin_preserves_IsCore`

**Repo:** markov-semigroups · **Status: not started**
**Effort: ~3–5 active days.**

Discharges the core-preservation axiom at
`MarkovSemigroups/Instances/WorkInProgress/EuclideanFin.lean:2771`. The
1D analogue was historically axiomatised and is now proved (commit `890e022`,
Path C Hermite IBP).

**Strategy** (per gemini-3.1-pro-preview vetting 2026-05-13, in AXIOM_AUDIT.md):
- Change of variables on the Mehler integral:
  `(P_t f)(x) = ∫ f(z) · ρ_t(x, z) dz` where `ρ_t(x, z)` is the shifted
  Gaussian density (C^∞ in x).
- Apply `ContDiff.integral` to push derivatives onto the kernel rather
  than `f`.
- Deliberately avoids the multi-index Hermite-IBP route (notoriously hard
  in Lean4 due to `iteratedFDeriv`'s symmetric-multilinear formulation).

---

### Workstream N1.c — `ouSemigroupFin_entropy_sq_decay_bound`

**Repo:** markov-semigroups · **Status: not started**
**Effort: ~3–5 active days.**

Discharges the entropy-decay axiom at
`MarkovSemigroups/Instances/WorkInProgress/EuclideanFin.lean:2799`. The
1D analogue is proved (commit `1b3f797`, A1+A2 decomposition).

**Strategy** (per gemini-3.1-pro-preview corrected discharge plan, AXIOM_AUDIT.md):
**Telescoping argument** (the naïve chain rule fails): peel one Mehler factor
`P_t^{(k)}` at a time and use γ_k-invariance to make the macroscopic
terms cancel across the *difference* `Ent(h) − Ent(P_t^{(k)} h)`, then
telescope over k and sum the 1D bounds. Per-step uses the proved
`Gaussian1D.bakryEmerySpace.semigroup_entropy_sq_decay_bound`.

---

### Route A — Abstract `gross_lsi_implies_hypercontractive`

**Repo:** markov-semigroups · **Status: not started (plan drafted by another agent)**
**Effort: ~1700–3000 lines, multi-week.**

Discharges the abstract Gross 1975 theorem at
`MarkovSemigroups/Abstract/Hypercontractivity.lean:269`. The "headline"
axiom — the one Mathlib doesn't have.

**Primary plan doc:** [`markov-semigroups/plans/gross-discharge.md`](https://github.com/mrdouglasny/markov-semigroups/blob/main/plans/gross-discharge.md)
(lives on markov-semigroups `main` via commits `ef272f6` and `6dc2026`;
not on the Phase 2 feature branch — see Branch chain section above).

**Plans index:** [`markov-semigroups/plans/README.md`](https://github.com/mrdouglasny/markov-semigroups/blob/main/plans/README.md)
catalogues both Route A and the superseded Route B alternative.

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
pphi2 (Workstream B in flight)
   ↓ imports
gaussian-hilbert (zero local axioms; Workstream C done)
   ↓ imports
markov-semigroups (Workstreams 2.5 + N1.b + N1.c + Route A live here)
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

**Parallel tracks (independent worktrees):**

1. **Workstream B in pphi2** — keep pushing; ~1–2 wk.
2. **Workstream 2.5 in markov-semigroups** — dispatch now (smallest, dual-vetted, ~1.5 days). Highest impact-per-effort.
3. **Workstream N1.b in markov-semigroups** — dispatch in parallel with 2.5; different file region, no conflict.
4. **Workstream N1.c in markov-semigroups** — dispatch in parallel; different file region.

**Route A:** vet the Phase 0 design with Gemini deep-think + Codex *before* touching the
`DirichletMarkovSemigroup` structure. The other agent flagged this as the
"one mistake that wastes the whole effort." After vetting, decide whether
to launch a dedicated Route A campaign (multi-week) or accept Gross as the
final inherited textbook axiom.

---

## Milestones

- **M1 (passes within ~2 wk):** Workstream B lands. pphi2 has **zero local
  axioms on the T² critical path**. Endpoint closure becomes the standard
  trio + 4 inherited markov-semigroups axioms. Defensible mathematical
  resting point.
- **M2 (passes within ~2 wk + Workstream 2.5):** Phase 2.5 lands. One
  inherited axiom drops (closure: trio + 3 markov-semigroups axioms).
- **M3 (passes within ~3 wk):** N1.b and N1.c land. Closure: trio +
  `gross_lsi_implies_hypercontractive` only. T² OS0–OS2 reduced to a single
  textbook axiom (Gross 1975).
- **M4 (multi-week from M3):** Route A lands. Closure: standard Mathlib
  trio only. **T² OS0–OS2 proved end-to-end in Lean modulo Mathlib's
  classical axioms.** This is the project's ultimate axiom-free milestone.

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

**Per-commit log of this campaign:** see `git log phase-b-discharge ^main`.
