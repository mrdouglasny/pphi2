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
| pphi2 axioms (real) | **19** | `count_axioms.sh` reports 22; 3 are docstring matches |
| pphi2 sorries | **0** | `count_axioms.sh` |
| gaussian-field axioms | **3** | `count_axioms.sh` |
| gaussian-field sorries | **0** | `count_axioms.sh` |

**Real-axiom breakdown (19 = 17 + 2):**
- **17 architectural** — enumerated by OS-program cluster in
  [`../planning/INDEX.md`](../planning/INDEX.md).
- **2 private scaffolding** — `asymTorusInteracting_exponentialMomentBound`
  (`Pphi2/AsymTorus/AsymTorusOS.lean`), `gaussian_rp_cov_perfect_square`
  (`Pphi2/OSProofs/OS3_RP_Lattice.lean`).

The superseded-chain `torus_weakCoupling_lattice_connectedFourPoint_strictNeg` axiom and
its sole consumer `torus_pphi2_isInteracting_weakCoupling` (carrier file
`Pphi2/TorusContinuumLimit/TorusInteractingResult.lean`) were **removed on 2026-06-21**
after Route A's `torus_pphi2_isInteractingStrict_weakCoupling` (PR #48, 2026-06-07)
subsumed them.

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
