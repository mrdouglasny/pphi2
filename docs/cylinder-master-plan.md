# Cylinder S¹×ℝ φ⁴₂ — master plan & progress tracker

**Created:** 2026-05-22 (after the T² OS0–OS2 endpoint reached the bare Mathlib trio —
see `docs/T2-master-plan.md`).
**Repo:** pphi2 (this) + sister repos gaussian-hilbert, markov-semigroups, OSreconstruction.
**Goal endpoint:** the P(φ)₂ measure on the **cylinder S¹(Lₛ) × ℝ** (finite spatial
circle, infinite Euclidean time) satisfies **OS0–OS4** — adding **reflection positivity
(OS3)** and **clustering / mass gap (OS4)**, which the compact torus deliberately could
not give. OS3 is what makes the cylinder the gateway to **OS reconstruction → a Wightman
QFT in 1+1d with a positive mass gap**.

This is the successor campaign to the torus. Per the calibration in the torus plan and
the heavy reuse below, the realistic horizon is **a few weeks** to unconditional OS0–OS3
and OS4-modulo-textbook-axioms; the genuine new crux (spectral-gap transfer to the
continuum) is the long pole.

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
Discharge the three conditions of `routeBPrime_cylinder_OS` **and** add OS1. Heavy reuse of
torus machinery and the existing cylinder adapters — much of this is integration, with one
genuine analytic piece (CYL-1a) and one real RP proof (CYL-1b).

- **CYL-1a `…HasUniformGreenMomentBound` (genuine analytic piece).** Exp-moment bound along
  the Lₜ-sequence, same shape as the torus `torusInteracting_exponentialMomentBound`. Reuse
  the **axiom-free** Nelson estimate + hypercontractivity (geometry-agnostic — see Reuse).
- **CYL-1b `…EventuallyReflectionPositive` — prove finite-stage pullback RP (the real RP
  work).** The CF-limit transfer is **already done**: `cylinderMeasureReflectionPositive_of_tendsto_cf`
  (`CylinderOS.lean:404`) plus the sequence adapters `.of_forall` (`:334`) and
  `.of_eventually_full` (`:347`). Do **not** re-derive the CF argument. The remaining task is
  to **prove RP for the finite cylinder pullback measures** (eventual full RP) by combining
  lattice RP `action_decomposition` (`OS3_RP_Lattice.lean`) with the weak-limit closure
  `rp_closed_under_weak_limit` (`OS3_RP_Inheritance.lean`) at the finite-Lₜ stage, then feed
  it through `.of_eventually_full`.
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
existing **axioms**. The axiom table alone understates the scope — the largest blocker is a
new theorem (CYL-2a), not an axiom.

**New theorems still to prove** (no current analogue):

| Obligation | Workstream | Gates | Note |
|---|---|---|---|
| spectral-gap transfer lattice→continuum | **CYL-2a** | OS4 | the crux / long pole; not an existing axiom |
| `LinearGrowth` witness for the cylinder OSPackage | **CYL-4a** | reconstruction | genuine analytic input, not implied by OS0–OS4 |
| OS1 transfer through the IR limit | **CYL-1d** | OS1 | extends the OS0 transfer; modest |
| finite-stage pullback RP | **CYL-1b** | OS3 | combines proved lattice RP + weak-limit closure |

**Existing axioms to discharge** (all textbook-vetted; CYL-3):

| Axiom | File:line | Gates | Source |
|---|---|---|---|
| `spectral_gap_uniform` | `TransferMatrix/SpectralGap.lean:89` | OS4 | Glimm-Jaffe-Spencer cluster expansion |
| `spectral_gap_lower_bound` | `TransferMatrix/SpectralGap.lean:100` | OS4 | Simon §III.2 |
| `two_point_clustering_from_spectral_gap` | `OSProofs/OS4_MassGap.lean:137` | OS4 | Reed-Simon IV XIII.44 |
| `general_clustering_from_spectral_gap` | `OSProofs/OS4_MassGap.lean:160` | OS4 | GRS 1975 II §IV; Glimm-Jaffe §6.2 |
| `rotation_cf_defect_polylog_bound` | `OSProofs/OS2_WardIdentity.lean:614` | (torus OS2 rotation; **not** needed for the cylinder, whose OS2 is translation+reflection only) | Glimm-Jaffe §19.2 |

OS0+OS1+OS2+OS3 on the cylinder need **no axioms** once CYL-1 lands. OS4 needs *both* the
CYL-2a new theorem *and* the four OS4 axioms above; reconstruction additionally needs CYL-4a.

---

## Recommended sequencing

1. **CYL-1** (a = the analytic exp-moment piece; b = finite-stage pullback RP fed to the
   existing CF transfer; c = OS2 wiring via `of_torusOS`; d = OS1 lane) →
   **`cylinder_satisfies_OS0123`**, unconditional cylinder OS0+OS1+OS2+OS3. Near-term, high
   reuse. *The satisfying first milestone — the first construction with reflection positivity.*
2. **CYL-2a** — spectral-gap transfer to the continuum. The hard analytic crux; budget the
   most time here (the cylinder's analogue of the Nelson/hypercontractivity work).
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
- `docs/T2-master-plan.md` — the completed torus OS0–OS2 construction (reusable infra + the
  axiom-free hypercontractivity chain).
- `docs/axiom_audit.md`, `AXIOM_AUDIT.md` (sister repos) — axiom provenance/vetting format.
