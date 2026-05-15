# T² φ⁴₂ continuum limit — proof analysis and roadmap

**Date:** 2026-05-13 (initial), refreshed 2026-05-15
**Repo:** pphi2 + sister repos (gaussian-field, gaussian-hilbert, markov-semigroups, bochner)
**Author:** Claude session log

---

## 0. Executive summary

The **T²_L torus φ⁴₂ continuum limit construction satisfying OS0–OS2** is
**structurally complete and builds end-to-end** (`lake build`, 3854 jobs).
The Lean module `Pphi2/TorusContinuumLimit/TorusInteractingOS.lean` carries
**0 local axioms and 0 sorries**. The full lattice-to-continuum existence
theorem `torusInteractingLimit_exists` is proved (Mitoma–Chebyshev tightness
+ Prokhorov + Nelson exponential moment uniformity), and OS0 (analyticity),
OS1 (regularity) and OS2 (translation + D4 invariance) all hold for the
limit measure.

What remains is **discharging the cross-cutting Glimm–Jaffe textbook
estimates** that the upstream layers axiomatise. The single critical-path
axiom on `torusInteracting_satisfies_OS` is currently
`polynomial_chaos_exp_moment_bridge` (the lattice Nelson exponential
estimate). After that discharges, transitive OU/Mehler placeholders
from gaussian-hilbert surface, plus the two Phase B Glimm–Jaffe Fourier
estimates introduced 2026-05-12 to close `rough_error_variance`.

**Recalibrated remaining effort to a 0-axiom T² OS0–OS2 construction
(modulo the standard Mathlib trio + 2 inherited markov-semigroups Gross
axioms):** roughly **3–5 weeks** of focused work across 2 parallel tracks
— substantially less than the 2026-05-13 estimate of 8–12 weeks. The
2026-05-13 → 2026-05-15 sister-repo work (markov-semigroups Lp-carrier
Phase 1+2 + gaussian-hilbert Phase 3 wire-in smoke test) collapsed
Workstream C from ~3–4 wk down to ~1–2 days of adapter code.

OS3 and OS4 are out of scope for Route B (the symmetric torus). They are
handled by Route B' (cylinder IR limit) and Route C (direct cylinder
construction); see `README.md` §4.

---

## 1. What is being proved

### 1.1 The target theorem

```lean
-- Pphi2/TorusContinuumLimit/TorusInteractingOS.lean (existing, 0 axioms, 0 sorries)
theorem torusInteractingLimit_satisfies_OS (...) : -- OS0 + OS1 + OS2 for the T²_L limit
```

For each polynomial interaction `P : InteractionPolynomial` (φ⁴₂ being the
canonical case), bare mass `m₀ > 0`, and physical volume `L > 0`:

1. The lattice measures `μ_{N,a,P,m₀}` on the configuration space
   `(ℤ/Nℤ)² → ℝ` (with `a = L/N`, fixed physical volume `L² = (Na)²`)
   form a tight family on the Polish torus configuration space.
2. Any subsequential weak limit `μ_{∞,P,m₀}` on the Polish T²_L
   configuration space exists.
3. The limit measure satisfies
   * **OS0** (analyticity of the generating functional in test
     functions),
   * **OS1** (Schwartz-norm regularity),
   * **OS2** (translation invariance + D4 dihedral symmetry).

OS3 (reflection positivity) and OS4 (mass gap) require a time direction,
which the symmetric T² doesn't have — handled by Routes B'/C.

### 1.2 The four-ingredient mathematical construction

```
                 ┌────────────────────────┐
                 │ Lattice GFF + e^{-V} ρ │   (existence: latticeMeasure)
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

* **Lattice GFF + φ⁴ Gaussian density** — `latticeGaussianMeasure d N a m₀`
  (in gaussian-field) + a `e^{-V}` density via `Pphi2/InteractingMeasure/`.
* **Tightness** — `continuumMeasures_tight` (in pphi2): proves the family
  of finite-N measures is tight on the Polish torus configuration space
  via Mitoma–Chebyshev + uniform second moments + Prokhorov on
  `Configuration` (which embeds into `ℕ → ℝ` via the DM basis).
* **Nelson's exponential bound** — `polynomial_chaos_exp_moment_bridge`
  (currently axiomatised in pphi2): the L²-norm of the Boltzmann weight
  `‖exp(-V_a)‖_{L²(μ_GFF)}` is bounded uniformly in `(a, N)`. This is the
  hardest analytical content; the canonical Glimm–Jaffe Ch. 8 dynamical
  cutoff proof requires the full polynomial-chaos / hypercontractivity
  machinery.
* **OS axiom transfer** — `TorusOSAxioms.lean` and
  `TorusInteractingOS.lean`: lattice OS axioms transferred through the
  weak limit via characteristic-functional convergence. **Already proved.**

### 1.3 What is genuinely novel here

The construction is the standard Glimm–Jaffe / Nelson route, with one
mathematical refinement: the choice of **fixing physical volume `L = N·a`**
rather than `a → 0` then `L → ∞`. This isolates the UV limit and avoids
the IR issues that plague the flat-ℝ² S'(ℝ²) approach. The tightness
proof on the Polish torus configuration space (`prokhorov_configuration`,
`prokhorov_configuration_sequential`) is **fully proved** rather than
axiomatised — this was a real gap in earlier formalisations.

---

## 2. Current state — what's done

### 2.1 The endpoint module

```
Pphi2/TorusContinuumLimit/TorusInteractingOS.lean:
  0 local axioms, 0 sorries.

  Provides:
  - torusInteractingLimit_exists  (existence via Prokhorov)
  - torusInteractingLimit_satisfies_OS  (OS0 + OS1 + OS2 for the limit)
```

### 2.2 The single non-builtin axiom in the transitive set

`#print axioms torusInteractingLimit_satisfies_OS` reports
**1 non-builtin axiom**:

```
polynomial_chaos_exp_moment_bridge
  (Pphi2/NelsonEstimate/PolynomialChaosBridge.lean:116)
```

plus the standard Mathlib trio (`propext`, `Classical.choice`, `Quot.sound`).

### 2.3 What's been discharged in this work cycle (recent)

| Lemma / theorem | When | Where | Status |
|---|---|---|---|
| `osgood_separately_analytic` | earlier | (proved) | OS0 input |
| `torusGeneratingFunctionalℂ_analyticOnNhd` | earlier | proved | Gaussian OS0 |
| `evalTorusAtSite_timeReflection` | earlier | proved upstream | OS2 |
| `evalTorusAtSite_latticeTranslation` | earlier | proved upstream | OS2 |
| `osgood_separately_analytic` (full proof) | earlier | 1965 lines, 0 axioms | OS0 |
| `prokhorov_configuration_sequential` | earlier | proved theorem | tightness |
| `polynomial_chaos_concentration` (Janson 5.10) | earlier | gaussian-hilbert | concentration |
| `gffOrthonormalProj_pushforward_eq_stdGaussian` | earlier | gaussian-field, proved | chaos bridge |
| `siteWickMonomial_eigenbasis_expansion` | earlier | gaussian-field, proved | chaos bridge |
| `canonicalCrossTerm_inner_eq_zero` (S3) | 2026-05-11 | RoughErrorBound.lean:407 | rough_error_variance |
| `canonicalRoughError_l2_sq_eq` (S3 composition) | 2026-05-11 | line 864 | rough_error_variance |
| `canonicalCrossTerm_l2_sq_le` (S4) | 2026-05-12 | line 1275 | rough_error_variance |
| **`rough_error_variance` (S5)** | 2026-05-12 | **line 1517, axiom-free modulo Phase B** | **the Step 1 of bridge** |
| Phase 0 helpers (heat-kernel 1D, partial) | 2026-05-12 | HeatKernelBound.lean:393–600 | Phase B Phase 0 |

### 2.4 Build status

`lake build` passes cleanly: 3854 jobs, 0 errors, modulo standard linter
suggestions. Pphi2 has **0 sorries** in the active build.

---

## 3. Remaining work to a fully axiom-free T² OS0–OS2 construction

Five distinct workstreams. They can be parallelised across repos.

### 3.1 Workstream A — discharge the 2 Phase B axioms in pphi2

**Files affected:** `Pphi2/NelsonEstimate/{HeatKernelBound,CovarianceBoundsGJ}.lean`,
+ supporting helpers in `FieldDecomposition.lean`.

| Axiom | What | Plan |
|---|---|---|
| `smoothWickConstant_le_log_uniform_in_aN` | `c_S ≤ A + B(1+\|log T\|)` uniform in (N,a) at fixed L | docs/phase-B-textbook-axioms.md (high-level), docs/phase-B-codex-handoff-2026-05-12.md (detailed Lean skeleton) |
| `canonicalRoughCovariance_pow_sum_le_uniform_in_aN` | `a^d Σ_y \|C_R(x,y)\|^m ≤ C_m·T` for all m≥1 | same docs; strategy verified by Gemini deep-think 2026-05-12 (docs/phase-B-deep-think-record-2026-05-12.md) — Fubini+semigroup for m=2, Minkowski for m≥3 |

**Status (2026-05-13):**
- Phase 0 helpers landed and compiling on `phase-b-discharge` branch
  (commit `27660f0`): `sin_pi_div_N_reflect`, `pi_j_div_N_le_half_pi`,
  `sin_sq_pi_k_div_N_ge_min_sq`, `exp_neg_t_sin_sq_le`. The key
  load-bearing per-term bound `exp(-t·4sin²(πk/N)/a²) ≤ exp(-16t·j²/L²)`
  is fully proved.
- Two documented sorries to fill (`sum_min_le_two_sum`,
  `heat_kernel_1d_bound_uniform` Steps 2–5).
- Comprehensive codex handoff plan in
  `docs/phase-B-codex-handoff-2026-05-12.md` covers the full
  Phases 0–5 with proof skeletons.

**Estimated effort:** 1100 lines, ~11 active days (~3 weeks wall-clock).

### 3.2 Workstream B — discharge `polynomial_chaos_exp_moment_bridge`

**File:** `Pphi2/NelsonEstimate/PolynomialChaosBridge.lean:116`.

The 6-step Glimm–Jaffe assembly. Steps 1, 2, 3 already in place via
existing helpers; remaining glue:

| Step | What | Status |
|---|---|---|
| 1 — covariance split `C = C_S + C_R` | done | `CovarianceSplit.lean`, `FieldDecomposition.lean` |
| 2 — Wick binomial decomposition `V = V_S + E_R` | infrastructure done | `WickBinomial.lean`, `FieldDecomposition.lean` |
| 3 — smooth-side classical bound `V_S ≥ -C(1+\|log T\|)²` | done | `smooth_interaction_lower_bound_log` |
| 4 — rough-side polynomial-chaos concentration | partially done | needs glue: push φ_R → standard Gaussian, identify in `wienerChaosLE`, apply `polynomial_chaos_concentration` |
| 5 — dynamical cutoff `T(M) := exp(-(√(M/2C₁) - 1))` | not done | doubly-exp tail in M |
| 6 — layer-cake integration | partial | `LayerCake.lean` has scaffolding |

**Plan:** `docs/polynomial-chaos-exp-moment-bridge-proof-plan.md` (537
lines). All 6 steps spelled out.

**Cross-repo deps available:** `polynomial_chaos_concentration`
(Janson 5.10) in gaussian-hilbert, `gffOrthonormalProj_pushforward_eq_stdGaussian`
+ `siteWickMonomial_eigenbasis_expansion` in gaussian-field.

**Estimated effort:** 300–500 lines, **~1–2 weeks** (per AXIOM_STATUS.md).
Best dispatched AFTER Workstream A so the rough-side L^p bounds become
real theorems instead of axioms.

### 3.3 Workstream C — discharge the OU/Mehler placeholder in gaussian-hilbert

**Status as of 2026-05-15: ~80% complete; ~1–2 active days remaining.**

**File:** `gaussian-hilbert/GaussianHilbert/OUEigenfunctions.lean` (axiom
`ouSemigroupAct_eLpNorm_hypercontractive`).

This is **Bonami–Beckner–Nelson hypercontractivity**:
`‖e^{-tL}f‖_{L^p} ≤ ‖f‖_{L²}` for `p ≤ 1 + e^{2t}` (Mehler's representation
+ Gaussian L²–L^p contractivity).

The discharge route is "Stage N" (multivariate BE → LSI → Gross), and the
heavy lifting is done in upstream layers. Current state of the dependency
chain (newest at top):

| Component | Status |
|---|---|
| Phase 3 wire-in smoke test in gaussian-hilbert | ✅ done 2026-05-15 (`phase-3-smoke-test`, commit `0f0c5eb`) |
| Lp-carrier Phase 2 in markov-semigroups (concrete `stdGaussianFin_dirichletMarkovSemigroup` bundle) | ✅ done 2026-05-15 (`feat/lp-carrier-stdGaussianFin-dirichletmarkov`, commit `6782dc7`) |
| Lp-carrier Phase 1 in markov-semigroups (abstract `MarkovSemigroup` / `DirichletMarkovSemigroup`) | ✅ on markov-semigroups main (`e1e2011`) |
| N1 multivariate Bakry-Émery instance in markov-semigroups | ✅ on markov-semigroups main (`e1e2011`) |
| Stage Ag agreement theorem `mehlerOp_eq_ouSemigroupAct` | ✅ done 2026-05-11 |
| **E.1** — `h_lsi` adapter (transfer `BakryEmerySpace.satisfiesLogSobolev` through the new bundle) | ❌ ~50–100 lines, ~0.5–1 day |
| **E.2** — predicate adapter (abstract `IsHypercontractive` → concrete `eLpNorm` form) | ❌ ~50 lines, ~0.5–1 day |

**Updated plan:** `gaussian-hilbert/docs/hypercontractivity-discharge-plan.md`
(refreshed 2026-05-15) — total-effort table revised after the 2026-05-13
→ 2026-05-15 work delivered most of Stage N's bridge. Stage W (LSI
tensorization shortcut) was the previous recommendation but is now
strictly worse: same time-to-completion, plus one new axiom in
markov-semigroups.

**Phase 2.5 follow-up (post-discharge cleanup):** Phase 2's
`energy_eq_deriv` was proved by polarization from the existing
markov-semigroups axiom `ouSemigroupFin_l2_sq_hasDerivWithinAt`, making
that axiom transitively visible at gaussian-hilbert's public bundle
boundary. Discharging it (1.5 active days, dual-vetted Fubini-lift
plan) drops markov-semigroups GaussianFin axiom count 11 → 10 and
removes the public-boundary exposure.

(Original wording — kept for historical context until next major
revision: ~325 lines, 4-stage plan with Stage A Mehler + Stage W
LSI-tensorization shortcut. Both have been overtaken by events.

- Stage A: Mehler operator semigroup laws (~200 lines, 3–5 days)
- Stage B: Markov-semigroup laws via BakryEmery hypercontractivity input
- Stage C/D: bridge to the spectral OU semigroup
- "Route W": uses `MarkovSemigroups.lsi_tensorize` upstream — would
  re-introduce the markov-semigroups dependency

**Estimated effort:** ~3–4 weeks per the README estimate.

### 3.4 Workstream D — pphi2 downstream OS-extension axioms (lattice-only)

These are NOT on the T² OS0–OS2 critical path but fill out the full
`torusInteracting_satisfies_OS` theorem to OS0–OS4 and the
S'(ℝ²) bridge:

| Axiom | File | What | Notes |
|---|---|---|---|
| `polynomial_chaos_exp_moment_bridge` | PolynomialChaosBridge.lean:116 | Nelson bound | **on critical path**, see Workstream B |
| `latticeGreenBilinear_basis_tendsto_continuum` | GaussianContinuumLimit/PropagatorConvergence.lean:103 | propagator continuum limit | task #164 (pending) |
| `continuum_exponential_moment_bound` | ContinuumLimit/AxiomInheritance.lean:123 | mixed L¹/Green exp moment for FLAT-ℝ² S' route | not Route B |
| `canonical_continuumMeasure_cf_tendsto` | ContinuumLimit/AxiomInheritance.lean:327 | CF convergence | not Route B |
| `continuum_exponential_clustering` | ContinuumLimit/AxiomInheritance.lean:354 | OS4 input | not Route B |
| `continuumLimit_nonGaussian` | ContinuumLimit/Convergence.lean:256 | nontriviality | needed for `pphi2_nontriviality` |
| `pphi2_nontriviality` | Main.lean:128 | non-Gaussianity wrapper | needed for full statement |
| `measure_determined_by_schwinger` | Bridge.lean:229 | moment determinacy on S'(ℝ²) | bridge to S'(ℝ²) route |
| `schwinger_agreement` | Bridge.lean:263 | concrete-construction agreement | bridge |
| `os2_from_phi4` | Bridge.lean:334 | S'(ℝ²) OS2 transfer | bridge |
| `rotation_cf_defect_polylog_bound` | OS2_WardIdentity.lean:614 | N-uniform polynomial-log a² bound | OS2 Ward identity refinement |

**Effort to fully discharge all:** unbounded — many of these (Bridge.lean
ones) are research-level questions requiring concrete S'(ℝ²) ↔ Polish-torus
moment-determinacy theorems which are themselves major projects.

### 3.5 Workstream E — pphi2 OS3 + OS4 (cylinder-time route, not Route B)

OS3 (reflection positivity) and OS4 (mass gap) on the cylinder
`S¹_L × ℝ` via Route B'/C. **Not part of the T² OS0–OS2 endpoint.**

Axioms:
- `asymTorusInteracting_exponentialMomentBound` (private, in
  AsymTorusOS.lean)
- `gaussian_rp_cov_perfect_square` (private, in OS3_RP_Lattice.lean)
- `spectral_gap_uniform`, `spectral_gap_lower_bound` (Cluster B,
  TransferMatrix/SpectralGap.lean)
- `two_point_clustering_from_spectral_gap`,
  `general_clustering_from_spectral_gap` (OS4_MassGap.lean)
- Route B' eventual Green-moment + RP inputs (in IRLimit/)

These are tracked separately in `docs/torus-route-gap-audit.md` and
the asymmetric-torus / cylinder docs.

---

## 4. Cross-repo dependency picture

```
                    ┌───────────────────────┐
                    │ pphi2 (this repo)     │
                    │ 19 axioms, 0 sorries  │
                    │ T² OS0-OS2: 1 axiom   │
                    │ on critical path      │
                    └──────────┬────────────┘
                               │
         ┌─────────────────────┼─────────────────────┐
         │                     │                     │
         ▼                     ▼                     ▼
┌──────────────────┐  ┌──────────────────┐  ┌──────────────────┐
│ gaussian-hilbert │  │  gaussian-field  │  │     bochner      │
│ 1 axiom (OU)     │  │ 3 axioms (off    │  │ infrastructure   │
│ Janson 5.10 ✓    │  │ T² critical path)│  │                  │
│ chaos files ✓    │  │ propagator ✓     │  │                  │
│ (Phase 3 wire-in │  │                  │  │                  │
│  smoke-tested)   │  │                  │  │                  │
└──────────┬───────┘  └──────────────────┘  └──────────────────┘
           │ (real import, post-2026-05-15 Phase 3 wire-in)
           ▼
┌──────────────────┐
│ markov-semigroups│
│ 11 axioms        │   Lp-carrier Phase 1+2 + N1 BE instance →
│ (3 GaussianFin   │   `stdGaussianFin_dirichletMarkovSemigroup`
│  + 2 Gross + 6   │   bundle (commit 6782dc7).
│  Cluster A)      │   On the T² critical path: 2 Gross axioms
│                  │   (transitive after Workstream C lands) +
│                  │   1 GaussianFin axiom load-bearing at the
│                  │   public boundary until Phase 2.5 cleanup.
└──────────────────┘
```

**Repo-by-repo on the T² OS0–OS2 critical path:**

| Repo | Axioms on T² OS0-OS2 critical path | Comments |
|---|---|---|
| pphi2 | **3** (`polynomial_chaos_exp_moment_bridge` + 2 Phase B Glimm-Jaffe) | Workstream A in flight (Phase 0 helpers landed) |
| gaussian-hilbert | **1** (`ouSemigroupAct_eLpNorm_hypercontractive`) | surfaces after pphi2 bridge discharges; Workstream C ~80% complete (E.1+E.2 adapters remain) |
| gaussian-field | **0** (3 axioms exist but for Schwartz/cylinder routes) | clean |
| markov-semigroups | **2 Gross axioms** (`gross_lsi_implies_hypercontractive` + transitive deps) **+ 1 GaussianFin axiom** (`ouSemigroupFin_l2_sq_hasDerivWithinAt`, polarization-introduced at public boundary, Phase 2.5 cleanup planned) | inherited via gaussian-hilbert post-Phase-3-wire-in |
| bochner | **0** (infrastructure only) | clean |

**Note:** This is much cleaner than the full pphi2 axiom count (19) suggests
— most pphi2 axioms are for the broader S'(ℝ²) bridge and OS3/OS4
extensions (Route B', C), not for the Route B T² OS0–OS2 endpoint.

**Note on the `require MarkovSemigroups` edges**: the 2026-05-13 prune
(commit `d419bc0` in pphi2) removed the *direct* dep that was vestigial
at that moment. Post-2026-05-15 the gaussian-hilbert side genuinely
imports MarkovSemigroups again (via `HypercontractivityFromBE.lean`),
but pphi2 still doesn't — the dep enters pphi2's transitive closure
only via gaussian-hilbert.

---

## 5. Recommended sequencing

(Refreshed 2026-05-15 after Workstream C collapsed to ~1–2 days.)

**Phase 1 (parallel, ~2–3 weeks):**
- **Track A:** Finish Workstream A (Phase B axioms in pphi2). In
  progress on `phase-b-discharge` branch; Phase 0 helpers landed
  (commit `27660f0`); ~9–10 days remaining per
  `docs/phase-B-codex-handoff-2026-05-12.md`.
- **Track C:** Finish Workstream C (OU/Mehler in gaussian-hilbert).
  Stage N's bridge work delivered upstream 2026-05-15 (markov-semigroups
  Lp-carrier Phase 2, gaussian-hilbert Phase 3 smoke test). Remaining:
  E.1+E.2 adapters, ~1–2 days per
  `gaussian-hilbert/docs/hypercontractivity-discharge-plan.md`.
- **(Optional) Track P2.5:** Phase 2.5 cleanup in markov-semigroups
  (fresh-Fubini lift to discharge `ouSemigroupFin_l2_sq_hasDerivWithinAt`,
  ~1.5 days). Eliminates the polarization-introduced public-boundary
  axiom and drops markov-semigroups GaussianFin axiom count 11 → 10.

**Phase 2 (after Phase 1, ~1–2 weeks):**
- **Workstream B:** Discharge `polynomial_chaos_exp_moment_bridge` using
  the now-real theorems from Tracks A and C. Plan in
  `docs/polynomial-chaos-exp-moment-bridge-proof-plan.md`.

**Phase 3 (verification, ~3–5 days):**
- `#print axioms torusInteractingLimit_satisfies_OS` should report only
  `[propext, Classical.choice, Quot.sound]` plus 2 inherited
  markov-semigroups Gross axioms (`gross_lsi_implies_hypercontractive`
  + transitively whatever `gross` brings) — that's the closure target
  for the milestone. The Gross axioms are textbook 1975 and have their
  own discharge plan in markov-semigroups.
- Update `AXIOM_AUDIT.md`, `docs/AXIOM_STATUS.md`, and `README.md`.
- Open final PR documenting the T² OS0–OS2 milestone.

**Total:** ~3–5 weeks wall-clock, parallelisable to ~3 weeks if Tracks
A and C run in tandem (since C is now ~1–2 days, A dominates the
critical path).

**Note on calibration:** these estimates use the `~/.claude/CLAUDE.md`
recalibrated formalization-time guidance (5–15× faster than community
norms once relevant infrastructure is in place — which it overwhelmingly
is here). Original 2026-05-13 estimate of "8–12 weeks" has been
roughly halved by the 2026-05-13 → 2026-05-15 sister-repo work.

---

## 6. Out of scope for this doc

- **Full OS0–OS4 T² theorem (with OS3, OS4):** requires Route B'
  (cylinder IR limit) or Route C (direct). Status of those is
  separately tracked in:
  * `docs/torus-route-gap-audit.md` (Route B' specifically)
  * `Pphi2/AsymTorus/`, `Pphi2/IRLimit/` files
  * Route C's 21 preserved axioms in `future/`.
- **The S'(ℝ²) flat-space alternative target:** `continuumLimit_exists`
  + `os0_for_continuum_limit` etc. in `ContinuumLimit/` —
  uses `continuum_exponential_moment_bound`, etc. (not Route B).
- **Nontriviality / non-Gaussianity:** `pphi2_nontriviality`,
  `continuumLimit_nonGaussian` — these are the `mass < c` weak-coupling
  cluster expansion content, a different research-level project.

---

## 7. Quick reference — discharge-plan documents

Critical-path:
* `docs/phase-B-textbook-axioms.md` — Phase B axiom proposals + Gemini
  vetting record
* `docs/phase-B-deep-think-record-2026-05-12.md` — verification of the
  C·T scaling for the rough-side bound, Fubini+semigroup + Minkowski
  proof routes
* `docs/phase-B-codex-handoff-2026-05-12.md` — concrete Lean proof
  skeleton for Phases 0–5 of Phase B discharge
* `docs/polynomial-chaos-exp-moment-bridge-proof-plan.md` — 6-step
  Glimm–Jaffe dynamical-cutoff plan for the master bridge axiom
* `docs/rough-error-variance-plan.md` — Step 1 of the bridge
  (`rough_error_variance`), now COMPLETED
* `gaussian-hilbert/docs/hypercontractivity-discharge-plan.md` —
  Stage N plan for the OU/Mehler placeholder axiom (refreshed
  2026-05-15: ~80% complete, ~1–2 days of E.1+E.2 adapters remain)
* `markov-semigroups/AXIOM_AUDIT.md` (Phase 2 entry) and
  `markov-semigroups/status.md` (2026-05-15 entry) — Lp-carrier
  Phase 2 deliverable + Phase 2.5 follow-up plan

Off-critical-path (Route B' / OS3+OS4 / S'(ℝ²)):
* `docs/torus-route-gap-audit.md` — Route B' status
* `docs/torus-interacting-os-proof.md` — the Route B proof overview

Audit and inventory:
* `AXIOM_AUDIT.md` — per-axiom audit + history
* `docs/AXIOM_STATUS.md` — current snapshot, by category
* `README.md` `## Current status` — one-paragraph rollup
