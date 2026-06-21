# Axiom Status Snapshot — superseded

> ⚠️ **This file is superseded as of 2026-06-21.** The master per-axiom status
> machine is [`../planning/INDEX.md`](../planning/INDEX.md). The historical log
> of audit passes and discharges is [`../AXIOM_AUDIT.md`](../AXIOM_AUDIT.md).
> Live raw counts come from `./scripts/count_axioms.sh`.
>
> This file used to be a consolidated snapshot. It accumulated drift faster
> than it could be refreshed and now serves only as a pointer.

## At a glance (2026-06-21)

| Count | Value | Source |
|---|---|---|
| pphi2 axioms (real) | **20** | `count_axioms.sh` reports 23; 3 are docstring matches |
| pphi2 sorries | **0** | `count_axioms.sh` |
| gaussian-field axioms | **3** | `count_axioms.sh` |
| gaussian-field sorries | **0** | `count_axioms.sh` |

**Real-axiom breakdown (20 = 17 + 2 + 1):**
- **17 architectural** — enumerated by OS-program cluster in
  [`../planning/INDEX.md`](../planning/INDEX.md).
- **2 private scaffolding** — `asymTorusInteracting_exponentialMomentBound`
  (`Pphi2/AsymTorus/AsymTorusOS.lean`), `gaussian_rp_cov_perfect_square`
  (`Pphi2/OSProofs/OS3_RP_Lattice.lean`).
- **1 superseded-chain axiom** — `torus_weakCoupling_lattice_connectedFourPoint_strictNeg`
  (`Pphi2/TorusContinuumLimit/TorusInteractingResult.lean`); consumed only by
  `torus_pphi2_isInteracting_weakCoupling` in the same file, which is itself superseded
  by Route A's `torus_pphi2_isInteractingStrict_weakCoupling` (2026-06-07, PR #48).
  Axiom + dead theorem should be removed together in the next cleanup pass.

**Docstring-match false positives** (`count_axioms.sh` regex catches the word
"axiom" at start of line, including inside docstrings):
- `Pphi2/NelsonEstimate/LatticeBridge.lean:21`
- `Pphi2/NelsonEstimate/LayerCake.lean:85`
- `Pphi2/AsymTorus/AsymExpMomentDischarge.lean:244`

## Where to look

- **Live status of each axiom**: [`../planning/INDEX.md`](../planning/INDEX.md).
- **History (what discharged when)**: [`../AXIOM_AUDIT.md`](../AXIOM_AUDIT.md).
- **Branch map** (which branch is live for which axiom):
  [`../BRANCHES.md`](../BRANCHES.md).
- **Coherence analysis** (the architectural gap A/B/C and keystone 18):
  [`../planning/coherence-analysis.md`](../planning/coherence-analysis.md).
