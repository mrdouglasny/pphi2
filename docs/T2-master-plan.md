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

## ⚠️ Branch chain & pin state (CRITICAL — audit-as-of 2026-05-17)

The campaign's work is spread across **feature branches in all three repos**.
pphi2's pins still point at each upstream's `main`, which **predates the
Workstream C, markov-semigroups Phase 2, and Route A work**. The current
`#print axioms` only shows `[trio + polynomial_chaos_exp_moment_bridge]`
because the bridge is still an axiom — opaque, so its (would-be)
transitive dependencies don't surface. When Workstream B converts the
bridge to a theorem, the closure will reflect **the pinned upstream**,
not the as-built feature-branch state.

| Repo | Active branch | HEAD | New work on branch | pphi2's pin | Pin currency |
|---|---|---|---|---|---|
| **pphi2** | `phase-b-discharge` | `d5d274a` | Workstreams A + B (incl. wickPolynomial_lower_bound_general blocker just landed) + master plan | — (self) | — |
| **gaussian-hilbert** | `phase-3-smoke-test` | `3a789d5` | Workstream C (E.1, E.2, axiom retirement, doc refresh) — 6 commits ahead of main | `main` (`85496cc`) | **pre-Workstream-C** |
| **markov-semigroups** | `feat/lp-carrier-stdGaussianFin-dirichletmarkov` | `aa9cc47` | Phase 2 bundle + **G2 complete + Gross-discharge scaffolding** (P2/P3 work in flight) — 6 commits ahead of main | `main` (`8ed9e528`, inherited via gaussian-hilbert) | **pre-Phase-2 and pre-Gross-scaffold** |

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
| C | OU/Mehler hypercontractivity (gaussian-hilbert) | gaussian-hilbert | ✅ COMPLETE 2026-05-15 (on `phase-3-smoke-test`) | merge to gaussian-hilbert main |
| **B** | `polynomial_chaos_exp_moment_bridge` (pphi2) | pphi2 | 🔄 in flight — blocker `wickPolynomial_lower_bound_general` resolved 2026-05-17; lift + narrow-signature refactor next | ~150–300 lines / ~1 wk |
| **2.5** | Fresh-Fubini lift for `ouSemigroupFin_l2_sq_hasDerivWithinAt` | markov-semigroups | not started | ~1.5 days |
| **N1.b** | `ouSemigroupFin_preserves_IsCore` | markov-semigroups | not started | ~3–5 days |
| **N1.c** | `ouSemigroupFin_entropy_sq_decay_bound` | markov-semigroups | not started | ~3–5 days |
| **Route A** | Abstract `gross_lsi_implies_hypercontractive` | markov-semigroups | 🔄 **G2 + Gross-ODE scaffolding done 2026-05-17**; P2/P3 algebra + W rewire in flight | ~weeks (was multi-week) |

**Total parallel wall-clock to fully zero-local-axiom T² endpoint:** ~3–5 weeks
if all five run in parallel; ~6–10 weeks serial. Route A still dominates the
critical path; G2-complete is a major architectural unblock.

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

**Repo:** markov-semigroups · **Status: 🔄 in flight (G2 complete + Gross-ODE scaffolding landed; P2/P3 work items in progress)**
**Effort remaining: ~weeks (P2/P3 algebra + W rewire).**

Discharges the abstract Gross 1975 theorem at
`MarkovSemigroups/Abstract/Hypercontractivity.lean:269`. The "headline"
axiom — the one Mathlib doesn't have.

**Primary plan doc:** [`markov-semigroups/plans/gross-discharge.md`](https://github.com/mrdouglasny/markov-semigroups/blob/main/plans/gross-discharge.md)
(lives on markov-semigroups `main` via commits `ef272f6` and `6dc2026`).

**Plans index:** [`markov-semigroups/plans/README.md`](https://github.com/mrdouglasny/markov-semigroups/blob/main/plans/README.md)
catalogues both Route A and the superseded Route B alternative.

**G2 + scaffolding landed 2026-05-17** (branch
`feat/lp-carrier-stdGaussianFin-dirichletmarkov`, 6 commits ahead of
markov-semigroups main, tip `aa9cc47`):

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
