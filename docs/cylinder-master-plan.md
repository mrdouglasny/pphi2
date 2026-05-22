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

## The target

An **unconditional** theorem `cylinder_satisfies_OS` : the cylinder φ⁴₂ measure satisfies
OS0, OS1, OS2, OS3, **and OS4** — i.e. discharge the three input hypotheses *and* add the
clustering/mass-gap output, ideally down to the bare Mathlib trio (as the torus reached),
realistically down to a small set of textbook-vetted axioms for the OS4 spectral input.

---

## Workstreams

### CYL-1 — Discharge the 3 conditional hypotheses ⇒ unconditional OS0+OS2+OS3
The fastest win; mostly reuses torus machinery.

- **CYL-1a `…HasUniformGreenMomentBound`.** Same shape as the torus exponential-moment
  bound (`torusInteracting_exponentialMomentBound`), now along the Lₜ-sequence. Reuse the
  **axiom-free** Nelson estimate + hypercontractivity (geometry-agnostic — see Reuse below).
- **CYL-1b `…EventuallyReflectionPositive`.** The key RP piece. Lattice RP
  (`action_decomposition`) and weak-limit closure (`rp_closed_under_weak_limit`) are proved;
  what's missing is the **explicit transfer**: show the asymmetric-torus pullback sequence's
  RP matrices are eventually nonneg (density/CF argument, parallel to the OS2 transfer).
- **CYL-1c `…HasCylinderOS2Symmetry`.** OS2 (translation + time reflection) is exact on the
  lattice torus; mirror the torus `…_gf_timeReflection_invariant` / translation proofs.

Outcome: `routeBPrime_cylinder_OS` applied to discharged hypotheses ⇒ **cylinder OS0+OS2+OS3
unconditional**.

### CYL-2 — OS4: clustering / mass gap (the substantial new work)
State and prove `cylinder_os4_clustering` (exponential decay of connected correlations as
Euclidean-time separation → ∞) ⇒ unique vacuum (ergodicity already proved). Pieces:
- **CYL-2a — spectral-gap transfer to the continuum (THE CRUX, genuinely new).** The
  transfer-operator spectral gap is proved on the *finite lattice*; OS4 on the cylinder needs
  the gap to survive the lattice→continuum (and Lₜ→∞) limit. No analogue exists yet — this is
  the cylinder's "Nelson-estimate-class" hard theorem. Likely the long pole.
- **CYL-2b — clustering from the gap.** Apply `two_point_clustering_from_spectral_gap` /
  `general_clustering_from_spectral_gap` (`OS4_MassGap.lean:137,160`) to the transferred gap,
  then `clustering_implies_ergodicity`. Mostly assembly once CYL-2a lands.

### CYL-3 — discharge the OS4 textbook axioms (mirror the Gross campaign)
All textbook-vetted (Reed-Simon XIII.44, Glimm-Jaffe §6.2/§19, Simon §III, GRS 1975), none
novel — the same situation the Gross axiom was in before this session. Targets:
- `spectral_gap_uniform`, `spectral_gap_lower_bound` (`TransferMatrix/SpectralGap.lean:89,100`)
- `two_point_clustering_from_spectral_gap`, `general_clustering_from_spectral_gap` (`OS4_MassGap.lean:137,160`)

These are the "down to the trio" stretch for OS4; like the Gross chain, each is a candidate
for either a full proof or a vetted textbook axiom with a discharge plan.

### CYL-4 — (stretch) OS reconstruction → Wightman
`Common/QFT/Euclidean/ReconstructionInterfaces.lean` defines the abstract OS↔Wightman
interface (`WickRotationPair`); the `OSreconstruction` sister repo holds the machinery. Once
cylinder OS0–OS4 is unconditional, instantiate reconstruction to obtain the 1+1d Wightman
theory with a mass gap. Out of scope until CYL-1/2/3 land.

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

## Axiom inventory gating cylinder OS0–OS4 (all textbook-vetted)

| Axiom | File:line | Gates | Source |
|---|---|---|---|
| `spectral_gap_uniform` | `TransferMatrix/SpectralGap.lean:89` | OS4 | Glimm-Jaffe-Spencer cluster expansion |
| `spectral_gap_lower_bound` | `TransferMatrix/SpectralGap.lean:100` | OS4 | Simon §III.2 |
| `two_point_clustering_from_spectral_gap` | `OSProofs/OS4_MassGap.lean:137` | OS4 | Reed-Simon IV XIII.44 |
| `general_clustering_from_spectral_gap` | `OSProofs/OS4_MassGap.lean:160` | OS4 | GRS 1975 II §IV; Glimm-Jaffe §6.2 |
| `rotation_cf_defect_polylog_bound` | `OSProofs/OS2_WardIdentity.lean:614` | (torus OS2 rotation; **not** needed for the cylinder, whose OS2 is translation+reflection only) | Glimm-Jaffe §19.2 |

OS0/OS2/OS3 on the cylinder need **no axioms** once CYL-1 is done. The five above are the OS4
debt (the first four), each textbook-vetted; CYL-3 is their discharge campaign.

---

## Recommended sequencing

1. **CYL-1** (a/c reuse torus + b is the RP transfer) → **unconditional cylinder OS0+OS2+OS3**.
   Near-term; high reuse. *This is the satisfying first milestone — the first construction
   with reflection positivity.*
2. **CYL-2a** — spectral-gap transfer to the continuum. The hard analytic crux; budget the
   most time here (the cylinder's analogue of the Nelson/hypercontractivity work).
3. **CYL-2b + CYL-3** — assemble OS4 from the transferred gap; discharge the OS4 textbook
   axioms toward the trio.
4. **CYL-4** — OS reconstruction → Wightman (sister-repo integration).

## Milestones

- **M-cyl-1:** `cylinder_satisfies_OS` proves OS0+OS2+OS3 **unconditionally** (CYL-1 done).
- **M-cyl-2:** OS4 clustering on the cylinder, modulo the textbook spectral/clustering axioms (CYL-2).
- **M-cyl-3:** OS4 axioms discharged — cylinder OS0–OS4 on the bare Mathlib trio (CYL-3).
- **M-cyl-4:** Wightman QFT (1+1d, mass gap) via OS reconstruction (CYL-4).

## Reference docs
- `docs/T2-master-plan.md` — the completed torus OS0–OS2 construction (reusable infra + the
  axiom-free hypercontractivity chain).
- `docs/axiom_audit.md`, `AXIOM_AUDIT.md` (sister repos) — axiom provenance/vetting format.
