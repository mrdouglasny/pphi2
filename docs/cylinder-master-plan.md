# Cylinder S¹×ℝ φ⁴₂ — master plan & progress tracker

> **STATUS UPDATE (2026-06-02) — B2 route locked as B1 ⊕ gap; transfer-matrix gap now PROVED.**
> The last project axiom `asymInteracting_expMoment_volume_uniform` reduces (Layer C, structural)
> to **Layer B2** = `asymInteractingVariance_le_freeVariance_Lt_uniform`. The discharge route is
> **B1 ⊕ gap** (authoritative; see `Pphi2/AsymTorus/AsymVarianceBound.lean`'s note and
> `docs/layer-B2-discharge-plan.md`):
> - **B1** (`asymInteractingVariance_le_freeVariance_torus`, **PROVED** via density-transfer /
>   Nelson **hypercontractivity**): `Var_int ≤ C(Lt)·Var_free`, `a`-uniform and norm-correct, but
>   **per-`Lt`**. This already supplies the UV / spatial-Sobolev matching.
> - **gap** (**PROVED** 2026-06-02): the cylinder transfer operator's operator-norm spectral gap —
>   `reflection-positivity` `GappedTransfer.susceptibility_le` + pphi2
>   `AsymGappedTransfer.lean` / `AsymSpectralGap.lean` (`asymGappedTransfer'`,
>   `asymTransferNormalized_gap`); prereq `AsymTransferGroundExcitedData.htop` (Perron-Frobenius
>   dominance) added. This supplies the `Lt` / IR uniformity (clustering; volume-independent).
> - **Remaining hard step (CORRECTED 2026-06-03 by the code map):** B2 = **B1 ⊕ gap ⊕
>   the Feynman–Kac bridge** — NOT a new textbook axiom. B2 fixes `Ls`, sends `Lt→∞`;
>   the only dangerous direction is time, owned by the **proved transfer-matrix gap**
>   (`susceptibility_le`, `Lt`-uniform), with **B1** owning the `a→0` UV uniformity at
>   fixed `Ls`. The genuine missing piece is the **measure↔transfer-operator
>   (Feynman–Kac) bridge** writing `∫(ωf)²dμ_int` as the gap-controlled time-sum
>   (deferred `transfer-operator-construction-todo`; scoped in
>   `docs/layer-B2-discharge-plan.md` → "Feynman–Kac bridge — scoping"), plus the
>   fixed-`Ls` gap convergence `m_a → m(Ls) > 0`.
> - **FSS infrared bound is PARKED for the later `Ls→∞` step, not B2** — it controls
>   the *spatial* infrared, which is gapped by the box at fixed `Ls`. Full vetted
>   statement + citation in `docs/fss-infrared-bound-spec.md`. DEAD ENDS (vetted):
>   Brascamp–Lieb (non-convex Wick double well), spectral-MEASURE domination
>   `ρ_int ≤ C·ρ_free` (mutually singular), GJ Ch. 9 form bound (lattice impedance
>   mismatch — fallback only).
>
> **Two corrections to the older framing below (both vetted, Codex + Gemini-3.1, 2026-06-02):**
> (1) **NO chessboard / FSS** — at fixed `Ls` the gap is uniform via compact-resolvent
> convergence; chessboard is only for the thermodynamic `Ls→∞` limit (see
> `reflection-positivity/docs/B2_UNIFORMITY_QUESTION.md`). So the "Layer B2 = UV chessboard,
> deferred" item in the 2026-05-31 banner is **superseded**. (2) The "fresh Källén-Lehmann
> *representation* axiom + cyclic-Young" idea and "Nelson **symmetry** (90° rotation)" are
> **dead ends** — spatial control is Nelson *hypercontractivity* (already in B1), not the rotation.
> **Do not write a representation axiom**; the route is B1 ⊕ gap. Full record + dead-ends:
> `docs/layer-B2-discharge-plan.md`.

> **STATUS UPDATE (2026-05-31) — isotropic redesign + one project axiom remaining.** The construction
> was rebuilt on an **isotropic `Z_Nt × Z_Ns` lattice** (single spacing `a`, periods `Lt=Nt·a`,
> `Ls=Ns·a`) to fix a metric inconsistency in the original square-via-geometric-mean approach.
> Current state on branch `cylinder-isotropic-lattice` (Phases 1b/2/3 **complete**):
> `cylinderIso_OS_of_RP_OS2` (`Pphi2/AsymTorus/AsymContinuumLimit.lean`) gives cylinder
> **OS0/OS1/OS2/OS3**, resting on **1 remaining project-introduced axiom** —
> `asymInteracting_expMoment_volume_uniform` (the CYL-1a Lₜ-uniform moment bound, deep-think-vetted
> 2026-05-27) — plus the two hypotheses `hRP` (OS3) and `hOS2`.
> `asymChaosCutoffDecomposition` (the UV Nelson chaos input) was **discharged 2026-05-31** (UNIT 7)
> via the trivial-split + pushforward + UNIT 2 + UNIT 6 route; see
> `asym-chaos-cutoff-decomposition-discharge-plan.md` and `Pphi2/AsymTorus/AsymNelson.lean`.
> `wickConstantAsym_eq_variance` was discharged 2026-05-27.
> **pphi2 branch: 20 raw / 18 real axioms, 0 sorries.**
>
> **Workstreams for the final axiom (parallel)** — see
> `asym-interacting-expmoment-volume-uniform-discharge-plan.md` for the full architecture:
>
> 1. **lee-yang repo** (new, Mathlib-only) — Layer A: Newman MGF Gaussian-domination
>    via Lee-Yang / Asano / Griffiths-Simon. Status: skeleton scaffolded at
>    `~/Documents/GitHub/lee-yang/` (README + PLAN + stubs); discharge-architecture
>    vet packet at `docs/asym-expmoment-discharge-via-lee-yang-vet-request.md`
>    awaiting gemini review before commit. ~1500-2500 lines Phase 1.
> 2. **pphi2 asym TM port** (this repo) — Layer B1: cylinder transfer matrix +
>    Källén-Lehmann variance bound (at fixed `a, Ns`). Status: Phase 1 done
>    2026-05-31 (`Pphi2/AsymTorus/AsymL2Operator.lean` — defs + compactness +
>    self-adjointness). Phases 2-4 pending. Plan:
>    `docs/asym-l2-operator-port-scoping.md`. ~900-1350 lines total.
> 3. **(deferred)** Chessboard / reflection-positivity infrastructure — Layer B2:
>    UV uniformity of the variance bound. Shares discharge path with the square's
>    open `spectral_gap_uniform`; not on the immediate critical path. Likely
>    home: new `reflection-positivity` repo eventually.
>
> Layer C (assembly, ~50 lines) glues Layers A + B2 once both land; discharges
> the axiom to a theorem.
>
> Current docs: `cylinder-isotropic-lattice-redesign.md` +
> `…-implementation.md` (construction), `cylinder-conditional-inputs-provability.md` (input map),
> `cylinder-os3-discharge-plan.md` (OS3 plan), and the per-axiom discharge plans cited above.
> The CYL-1a / CYL-2a framing below is still the right mental model (the two deep theorems = §4
> moment bound + OS4 spectral gap); the workstream details are reorganized in those newer docs.

**Created:** 2026-05-22 (after the T² OS0–OS2 endpoint reached the bare Mathlib trio —
see `docs/T2-master-plan.md`).
**Reviewed:** 2026-05-22, Gemini deep-think (2 ultrareview passes + a strategy vetting) —
verdict: architecture sound. Folded in: axiomatize CYL-1a for M-cyl-1, exact-reflection-symmetry
audit for CYL-1b, and `a`-independent gap as a prerequisite of CYL-2a.
**Repo:** pphi2 (this) + sister repos gaussian-hilbert, markov-semigroups, OSreconstruction.
**Goal endpoint:** the P(φ)₂ measure on the **cylinder S¹(Lₛ) × ℝ** (finite spatial
circle, infinite Euclidean time) satisfies **OS0–OS4** — adding **reflection positivity
(OS3)** and **clustering / mass gap (OS4)**, which the compact torus deliberately could
not give. OS3 is what makes the cylinder the gateway to **OS reconstruction → a Wightman
QFT in 1+1d with a positive mass gap**.

This is the successor campaign to the torus, and much of the *scaffolding* is reused — but
unlike the torus (a fixed-volume UV limit), the cylinder is an **infinite-volume (Lₜ→∞)
limit**, so it has two genuinely-new deep analytic theorems, not just plumbing: the
**Lₜ-uniform exponential-moment bound** (CYL-1a — gating OS0/OS1) and the **spectral-gap
transfer to the continuum** (CYL-2a — gating OS4). Either may need constructive-QFT locality
machinery (cluster expansion / correlation inequalities / chessboard estimates) or a textbook
axiom. So the timeline is **not** "a few weeks of reuse": the integration/wiring pieces are
near-term, but **M-cyl-1 (unconditional OS0–OS3) is gated on CYL-1a**, which is a real
infinite-volume-control theorem and the first hard bottleneck. Forecast honestly: near-term
*modulo* the Lₜ-uniform input.

---

## Current state — OS0+OS2+OS3 already PROVED (conditionally)

`Pphi2/IRLimit/CylinderOS.lean` — **`routeBPrime_cylinder_OS`** (line ~460) is a
**proved theorem**: the cylinder (S¹(Lₛ)×ℝ, obtained as the IR limit Lₜ → ∞ of the
asymmetric torus T²(Lₜ×Lₛ)) satisfies

- **OS0** (analyticity) — from uniform exponential moments + bounded-continuous convergence,
- **OS2** (time translation, time reflection, spatial translation) — exact at every finite
  Lₜ, transferred through the weak limit,
- **OS3** (reflection positivity) — transferred from the asymmetric-torus sequence via
  characteristic-functional convergence,

**conditionally on three input hypotheses** it currently takes as arguments:

| Hypothesis | Meaning | Status |
|---|---|---|
| `AsymTorusSequenceHasUniformGreenMomentBound` | Green-controlled uniform exp. moments along the Lₜ-sequence | input (to discharge) |
| `CylinderMeasureSequenceEventuallyReflectionPositive` | each fixed RP matrix is *eventually* nonneg along the sequence | input (to discharge) |
| `AsymTorusSequenceHasCylinderOS2Symmetry` | OS2 translation + time reflection per torus measure | input (to discharge) |

Supporting results **already proved**:
- `asymTorusInteracting_satisfies_OS` (`AsymTorus/AsymTorusOS.lean:2196`) — asymmetric-torus OS0/OS1/OS2.
- Lattice RP via the action decomposition `S = S⁺ + S⁻∘Θ` — `OSProofs/OS3_RP_Lattice.lean` (`action_decomposition`).
- RP closed under weak limits — `OSProofs/OS3_RP_Inheritance.lean` (`rp_closed_under_weak_limit`).
- `cylinderMeasureReflectionPositive_of_tendsto_cf` (`IRLimit/CylinderOS.lean:404`) — eventual-finitewise-RP + CF convergence ⇒ limit is RP.
- Ergodicity from clustering — `OSProofs/OS4_Ergodicity.lean` (`clustering_implies_ergodicity`), fully proved.
- Transfer matrix: positivity-improving + Jentzsch (simple positive ground state) + self-adjoint + compact + spectral gap `m_phys = E₁−E₀ > 0` — `TransferMatrix/Jentzsch.lean`, `JentzschProof.lean`, `SpectralGap.lean:65`.

`routeBPrime_cylinder_OS` makes **no OS4 claim** yet.

---

## The target — two distinct named endpoints (do not conflate)

- **`cylinder_satisfies_OS0123`** (milestone M-cyl-1): the cylinder φ⁴₂ measure satisfies
  **OS0, OS1, OS2, OS3 unconditionally**. `routeBPrime_cylinder_OS` currently delivers OS0,
  OS2, OS3 *conditionally* and does **not** output OS1 — so this endpoint needs both the
  three conditions discharged and an OS1 lane added (CYL-1d).
- **`cylinder_satisfies_OS`** (full endpoint): adds **OS4**. Ideally down to the bare Mathlib
  trio (as the torus reached), realistically modulo the new spectral-gap-transfer theorem
  (CYL-2a) and a small set of textbook-vetted OS4 axioms (CYL-3).

(Reserve the two names accordingly — `cylinder_satisfies_OS` is the OS0–OS4 endpoint, *not*
the partial M-cyl-1 theorem.)

---

## Workstreams

### CYL-1 — unconditional OS0+OS1+OS2+OS3  (`cylinder_satisfies_OS0123`, M-cyl-1)
Discharge the three conditions of `routeBPrime_cylinder_OS` **and** add OS1. Two of the four
items are integration/wiring (CYL-1c, CYL-1d) and one is a contained RP proof (CYL-1b) — but
**CYL-1a is a genuine constructive-QFT bottleneck (infinite-volume control), not free reuse**,
and it gates M-cyl-1. Do not treat M-cyl-1 as "a few weeks" without qualifying on CYL-1a.

- **CYL-1a `…HasUniformGreenMomentBound` — the IR/volume-uniformity bottleneck (HARD).** The
  cylinder is the **Lₜ→∞ (infinite-volume) limit**, so the exponential-moment bound must hold
  with constants **uniform in the time extent Lₜ**, not merely uniform in the lattice spacing.
  The repo's own `AsymTorus/MomentBoundOS1.lean` is explicit (its docstring + the "Caveat on
  Lt-uniformity"): deriving the Lₜ-uniform `K, C` is **not** an elementary consequence of
  Nelson's estimate + Cauchy-Schwarz — the naive transfer leaves explicit volume (Lₜ) growth.
  - **What IS done:** the *reduction* — `cylinderPullback_expMoment_uniform_bound` composes a
    per-measure Green-controlled bound `MeasureHasGreenMomentBound` with
    `torusGreen_uniform_bound` (gaussian-field) to yield the exact uniform cylinder-seminorm
    bound `routeBPrime_cylinder_OS` consumes. So the IR-limit step is wired.
  - **What is MISSING (the real obstruction):** proving the concrete UV-limit asymmetric-torus
    measures satisfy `MeasureHasGreenMomentBound` with constants **uniform in Lₜ**. This is the
    infinite-volume/locality control of constructive QFT — a full Lean proof requires locality
    machinery (cluster expansion, correlation inequalities, or chessboard estimates). This is
    the cylinder's first deep analytic theorem and the dominant risk to M-cyl-1's timeline —
    comparable in weight to CYL-2a, and arguably the gating item for OS0/OS1 themselves.
  - **DECISION for M-cyl-1 (Gemini deep-think, 2026-05-22): axiomatize, don't grind.**
    Formalizing a cluster expansion from scratch is a months-scale undertaking that would
    bottleneck the whole campaign. For the M-cyl-1 release, encapsulate the Lₜ-uniform bound as
    a **single dedicated Glimm-Jaffe axiom** (a `GlimmJaffe`-namespaced axiom / axiom class —
    e.g. `GlimmJaffe.asymTorus_uniformGreenMoment`, stated exactly as the missing
    `…HasUniformGreenMomentBound` input, vetted DT/GR, with a discharge-plan docstring citing
    Glimm-Jaffe Part III). This isolates the analytic debt cleanly while letting the entire
    OS0–OS3 structural wiring compile and be verified end-to-end. The cluster-expansion *proof*
    of this axiom then becomes a separate, deferred discharge campaign (a CYL-3-class item), to
    be tackled only after the structure is locked — exactly the pattern that retired the Gross
    axiom on the torus side.
  - **Discharge routes for the deferred CYL-1a axiom (when its proof is eventually attempted),
    ranked.** *Do not default to cluster expansion* — its combinatorics (polymer models,
    Mayer/tree expansions, activity bounds) is the least Lean-friendly genre in constructive
    QFT (single-use, bookkeeping-heavy). In **d=2** the field needs only Wick ordering (no
    regularity structures / paracontrolled UV machinery — that debt is a 3D problem). Ranked:
    1. **Finite-dimensional Boué–Dupuis / Gibbs variational formula at the lattice (LEAD).**
       Key realization (Gemini deep-think, 2026-05-22): Boué–Dupuis is a representation theorem
       for the Laplace transform of a **Gaussian measure**, *not* an SPDE result — so applied to
       the *finite lattice* (where the regularized measure is a high-dimensional multivariate
       Gaussian) it is just **finite-dimensional Gaussian IBP + Cameron–Martin/Girsanov-shift +
       convex optimization** — Donsker–Varadhan / Gibbs duality
       `−log E_μ[e^{−V}] = inf_u E[V(φ+u) + ½‖u‖²_{CM}]`. **No Itô, no Wiener space, no
       regularity structures.** Prove the bound at the lattice with constants **uniform in the
       dimension** (both the UV `N→∞` at fixed `L` and the IR `Lₜ→∞`) via a *local* test drift
       cancelling the Wick-ordered φ⁴ → the RHS is **extensive** (volume-linear) → uniform after
       dividing by volume; the bound then passes through both limits. d=2 Wick ordering is the
       only UV subtlety, absorbed by the drift. **The finite-dim pieces are exactly in-house:**
       `gaussianFin_integrationByParts` (proved this session) and `gaussian_cameronMartin`
       (markov-semigroups). Higher-leverage than cluster expansion: the variational formula is
       *universal* (scales to Φ⁴₃, gauge theories), not a weakly-coupled-lattice one-off.
    2. **FKG / correlation inequalities** (in-house: `gaussian-field` FKG, released) — cheap
       *assist* for volume-monotone second moments / tightness; may not reach the full
       exponential moment alone, but useful in combination.
    3. **LSI / Bakry–Émery for the Φ⁴₂ generator** — same entropy/variational circle as route 1
       (LSI ⇔ a log-Sobolev/entropy inequality). **Unifying payoff:** an LSI for the Φ⁴₂ measure
       (extending the just-completed Gaussian Bakry–Émery machinery to the φ⁴ generator) would
       yield **both CYL-1a and CYL-2a** (the mass gap) in one framework — also finite-dim at the
       lattice. The deepest investment, the biggest reuse.
    4. **Cluster expansion (Glimm-Jaffe-Spencer)** — classical fallback only; worst prover fit.
    (Gemini deep-think, 2026-05-22: keep axiomatized for M-cyl-1; for the eventual proof, the
    **finite-dimensional** variational formula bypasses the SPDE/stochastic-calculus library
    entirely and is the most elegant + structurally sound Lean path — investment, not
    from-scratch combinatorics.)
- **CYL-1b `…EventuallyReflectionPositive` — prove finite-stage pullback RP (the real RP
  work).** The CF-limit transfer is **already done**: `cylinderMeasureReflectionPositive_of_tendsto_cf`
  (`CylinderOS.lean:404`) plus the sequence adapters `.of_forall` (`:334`) and
  `.of_eventually_full` (`:347`). Do **not** re-derive the CF argument. The remaining task is
  to **prove RP for the finite cylinder pullback measures** (eventual full RP) by combining
  lattice RP `action_decomposition` (`OS3_RP_Lattice.lean`) with the weak-limit closure
  `rp_closed_under_weak_limit` (`OS3_RP_Inheritance.lean`) at the finite-Lₜ stage, then feed
  it through `.of_eventually_full`.
  - *Caveat (Gemini):* lattice RP needs **exact** reflection symmetry of the discrete action
    across the reflection plane. Audit the lattice derivative / link displacements / plaquette
    anchors for any geometric asymmetry across `t ↦ −t` — a discrete artifact there breaks
    `action_decomposition` and would also doom the CYL-2a transfer (which leans on the same
    reflection symmetry). Watch the `FinLatticeSites = Fin d → Fin N` vs `Fin Nₜ × Fin Nₛ`
    indexing mismatch noted in the OS3 file.
- **CYL-1c `…HasCylinderOS2Symmetry` — integration, largely done.** The bridge
  `AsymTorusSequenceHasCylinderOS2Symmetry.of_torusOS` (`CylinderOS.lean:380`) already
  projects the exact OS2 translation + time-reflection clauses from the bundled
  asymmetric-torus OS package. Task = use-site wiring, **not** a fresh proof campaign.
- **CYL-1d — OS1 (regularity) lane (NEW; required by the target).** `routeBPrime_cylinder_OS`
  does not currently output OS1, but the asymmetric torus proves it
  (`asymTorusInteracting_os1` / `AsymTorusOS1_Regularity`, `AsymTorusOS.lean:979`). Extend the
  IR-limit transfer to carry the OS1 regularity bound through Lₜ→∞ (analogous to the OS0
  transfer — both rest on the same uniform exponential-moment input from CYL-1a) and add OS1
  to the cylinder endpoint bundle.

Outcome: **`cylinder_satisfies_OS0123`** — cylinder OS0+OS1+OS2+OS3 unconditional (M-cyl-1).

### CYL-2 — OS4: clustering / mass gap (the substantial new work)
State and prove `cylinder_os4_clustering` (exponential decay of connected correlations as
Euclidean-time separation → ∞) ⇒ unique vacuum (ergodicity already proved). Pieces:
- **CYL-2a — spectral-gap transfer to the continuum (THE CRUX — a genuinely NEW theorem, no
  current analogue).** The transfer-operator spectral gap is proved on the *finite lattice*;
  OS4 on the cylinder needs the gap to survive the lattice→continuum (and Lₜ→∞) limit. This is
  the cylinder's "Nelson-estimate-class" hard theorem and the **single largest blocking
  obligation of the OS4 endpoint** — it is *not* one of the existing textbook axioms (see the
  inventory). Likely the long pole.
  - *Caveat (Gemini):* the continuum limit is delicate precisely because the bare gap can
    scale with the spacing `a`. **Decouple the gap from `a` first** — i.e. land
    `spectral_gap_uniform` (a lower bound independent of `a`, `SpectralGap.lean:89`) *before*
    attempting CYL-2a; transferring an `a`-dependent gap to the continuum is meaningless. So
    CYL-3's `spectral_gap_uniform` is effectively a prerequisite of CYL-2a, not parallel to it.
- **CYL-2b — clustering from the gap.** Apply `two_point_clustering_from_spectral_gap` /
  `general_clustering_from_spectral_gap` (`OS4_MassGap.lean:137,160`) to the transferred gap,
  then `clustering_implies_ergodicity`. Mostly assembly once CYL-2a lands.

### CYL-3 — discharge the OS4 textbook axioms (mirror the Gross campaign)
All textbook-vetted (Reed-Simon XIII.44, Glimm-Jaffe §6.2/§19, Simon §III, GRS 1975), none
novel — the same situation the Gross axiom was in before this session. Targets:
- `spectral_gap_uniform`, `spectral_gap_lower_bound` (`TransferMatrix/SpectralGap.lean:89,100`)
- `two_point_clustering_from_spectral_gap`, `general_clustering_from_spectral_gap` (`OS4_MassGap.lean:137,160`)

These are the "down to the trio" stretch for OS4; like the Gross chain, each is a candidate
for either a full proof or a vetted textbook axiom with a discharge plan. (Note: CYL-2a is a
separate, *new* obligation — discharging these four axioms does **not** by itself close OS4.)

### CYL-4 — OS reconstruction → Wightman (packaging THEN invocation)
The reconstruction interface is **not** "OS0–OS4 ⇒ Wightman" directly:
`ReconstructionLinearGrowthModel` (`Common/QFT/Euclidean/ReconstructionInterfaces.lean:36`)
requires a packaged `OSPackage` **together with a `LinearGrowth` witness**
(`linear_growth : LinearGrowth os_package`, line 46) before the reconstruction rule fires.
So two stages:
- **CYL-4a — package + linear growth.** Bundle the cylinder OS0–OS4 data into the project's
  `OSPackage`, and **prove the `LinearGrowth` hypothesis** for the cylinder measure — the
  extra growth input the OS axioms do not supply (polynomial growth bounds on the Schwinger
  functions; Glimm-Jaffe / OS-II). A genuine analytic obligation, not free.
- **CYL-4b — invoke reconstruction.** With the package + growth witness, instantiate
  `ReconstructionLinearGrowthModel` to obtain the 1+1d Wightman theory with mass gap
  (sister-repo `OSreconstruction`). Out of scope until CYL-1/2/3 land.

---

## Reusable from the torus (geometry-agnostic — already axiom-free)

- **Nelson exponential estimate** (`NelsonEstimate/`) — `∫ e^{−2V} dμ_GFF ≤ K` uniform in
  spacing; holds for any 2D lattice with confining potential. **Reuse directly.**
- **Hypercontractivity** (`ContinuumLimit/Hypercontractivity.lean`) — now **axiom-free** (the
  whole Gross→Bakry-Émery chain landed this session). **Reuse directly.**
- **Tightness / Prokhorov** (`ContinuumLimit/Tightness.lean`, `GaussianContinuumLimit/`) —
  uniform moments ⇒ weak limit. **Reuse directly.**

Torus-specific (needs a cylinder analogue): the lattice→continuum **embedding**
(`TorusContinuumLimit/TorusEmbedding.lean` vs the cylinder's time-periodization in
`IRLimit/CylinderEmbedding.lean`).

---

## Blocking obligations (two kinds: new theorems + textbook-vetted axioms)

Reaching the full OS0–OS4 endpoint on the trio requires **new theorems** *and* discharging
existing **axioms**. The axiom table alone understates the scope — **two** of the blockers are
deep new theorems (CYL-1a and CYL-2a), and one of them (CYL-1a) gates even the *first*
milestone OS0/OS1, not just OS4.

**New theorems still to prove** (no current analogue) — ordered by difficulty:

| Obligation | Workstream | Gates | Difficulty |
|---|---|---|---|
| **Lₜ-uniform** Green-controlled exp-moment bound (infinite-volume control) | **CYL-1a** | OS0, OS1 | **HARD** — likely cluster expansion / correlation inequalities / chessboard, or an upstream axiom; the reduction is wired, the uniform-in-Lₜ input is not. Gates M-cyl-1. |
| spectral-gap transfer lattice→continuum | **CYL-2a** | OS4 | **HARD** — the OS4 crux / long pole; not an existing axiom |
| `LinearGrowth` witness for the cylinder OSPackage | **CYL-4a** | reconstruction | medium — genuine analytic input, not implied by OS0–OS4 |
| OS1 transfer through the IR limit | **CYL-1d** | OS1 | modest — extends the OS0 transfer (but itself rests on CYL-1a) |
| finite-stage pullback RP | **CYL-1b** | OS3 | contained — combines proved lattice RP + weak-limit closure |

**Existing axioms to discharge** (all textbook-vetted; CYL-3):

| Axiom | File:line | Gates | Source |
|---|---|---|---|
| `spectral_gap_uniform` | `TransferMatrix/SpectralGap.lean:89` | OS4 | Glimm-Jaffe-Spencer cluster expansion |
| `spectral_gap_lower_bound` | `TransferMatrix/SpectralGap.lean:100` | OS4 | Simon §III.2 |
| `two_point_clustering_from_spectral_gap` | `OSProofs/OS4_MassGap.lean:137` | OS4 | Reed-Simon IV XIII.44 |
| `general_clustering_from_spectral_gap` | `OSProofs/OS4_MassGap.lean:160` | OS4 | GRS 1975 II §IV; Glimm-Jaffe §6.2 |
| `rotation_cf_defect_polylog_bound` | `OSProofs/OS2_WardIdentity.lean:614` | (torus OS2 rotation; **not** needed for the cylinder, whose OS2 is translation+reflection only) | Glimm-Jaffe §19.2 |

OS0+OS1+OS2+OS3 on the cylinder add **no new axioms** once CYL-1 lands — *provided CYL-1a is
proved* (if instead the Lₜ-uniform moment bound is taken as a textbook axiom, that one axiom
gates OS0/OS1). OS4 needs *both* the CYL-2a new theorem *and* the four OS4 axioms above;
reconstruction additionally needs CYL-4a.

---

## Recommended sequencing

1. **CYL-1** → **`cylinder_satisfies_OS0123`**, unconditional cylinder OS0+OS1+OS2+OS3.
   The wiring pieces are near-term (b = finite-stage pullback RP fed to the existing CF
   transfer; c = OS2 via `of_torusOS`; d = OS1 lane). For CYL-1a — the Lₜ-uniform exp-moment
   bound — the **decided path (Gemini deep-think) is to axiomatize**: introduce the dedicated
   `GlimmJaffe`-namespaced uniform-moment axiom and build M-cyl-1 on it now, deferring the
   cluster-expansion proof to a later discharge campaign. So M-cyl-1 is genuinely near-term;
   the analytic debt is isolated to one vetted axiom. *The reward: the first construction with
   reflection positivity.*
2. **CYL-3 `spectral_gap_uniform` (gap independent of `a`) → then CYL-2a** — spectral-gap
   transfer to the continuum. The `a`-independent gap is a *prerequisite* of the transfer
   (transferring an `a`-dependent gap is meaningless), so do it first. CYL-2a is then the
   second hard analytic crux (OS4); budget time comparable to CYL-1a's eventual proof.
3. **CYL-2b + CYL-3** — assemble OS4 from the transferred gap; discharge the four OS4 textbook
   axioms toward the trio.
4. **CYL-4a then CYL-4b** — package + prove `LinearGrowth`, then invoke reconstruction →
   Wightman (sister-repo integration).

## Milestones

- **M-cyl-1:** `cylinder_satisfies_OS0123` proves OS0+OS1+OS2+OS3 **unconditionally** (CYL-1 done).
- **M-cyl-2:** `cylinder_satisfies_OS` — adds OS4 clustering, modulo the CYL-2a spectral-gap-transfer theorem + the textbook OS4 axioms (CYL-2).
- **M-cyl-3:** the CYL-2a theorem proved and the OS4 axioms discharged — cylinder OS0–OS4 on the bare Mathlib trio (CYL-3).
- **M-cyl-4:** Wightman QFT (1+1d, mass gap) — package + `LinearGrowth` (CYL-4a) then OS reconstruction (CYL-4b).

## Reference docs
- `docs/layer-B2-discharge-plan.md` — **the live B2 discharge plan (B1 ⊕ gap route)**, with the
  full vetting record and the marked dead-ends (representation axiom, Nelson symmetry, chessboard).
- `docs/T2-master-plan.md` — the completed torus OS0–OS2 construction (reusable infra + the
  axiom-free hypercontractivity chain).
- `docs/axiom_audit.md`, `AXIOM_AUDIT.md` (sister repos) — axiom provenance/vetting format.
