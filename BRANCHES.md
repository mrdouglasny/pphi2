# Branch & thread map — where the live work is

Concise navigational map of pphi2's in-flight branches and the axiom each targets.
For the full per-axiom status machine see [`planning/INDEX.md`](planning/INDEX.md); for the
axiom inventory see [`docs/AXIOM_STATUS.md`](docs/AXIOM_STATUS.md).

> **Re-read this before resuming after a break.** It exists because on 2026-06-07 two inherited
> directives were found chasing **superseded** branches while the live frontier was elsewhere. Check
> this map before trusting a hand-off about "the current task".

## Active focus — the cylinder (Route B′), Layer B2

- **`main`** is canonical and carries the live cylinder work. **Axiom 3**
  `asymInteractingVariance_le_freeVariance_Lt_uniform` (`AsymExpMomentDischarge.lean:87`): the
  transfer-matrix Feynman–Kac machinery is **built and sorry-free** on `main`
  (`Pphi2/AsymTorus/Asym*` — `AsymTraceBridge` operator-decay bricks, `AsymGappedTransfer` proved gap,
  `AsymVarianceDischarge` B3 path-measure bridge, B4 susceptibility engine, `AsymTransferKernelOperator`).
  **Remaining gap** (the axiom still stands): wire B3→B4→B5 — apply the trace dictionary to the
  path-measure second moment + Hilbert–Schmidt trace-class + **B5b** single-slice stability + the
  `1/a` cancellation. **Live plan: [`docs/B4B5-design.md`]** + INDEX item 3. This is the nearest
  concrete win. Work on `main` (or a fresh branch off it).

## Done — non-Gaussianity (axiom 9), axiom-free

- **`route-a-weak-coupling`** (PR #48) — **DONE, axiom-free.** `torus_pphi2_isInteractingStrict_weakCoupling`
  (`TorusContinuumLimit/TorusCouplingResult.lean`): φ⁴₂ on T² is non-Gaussian (`u₄ < 0`) at weak
  coupling; `#print axioms ⟹ [propext, Classical.choice, Quot.sound]`. Reuses the proved
  `lattice_u4_neg_uniform` via a coupling-family continuum limit (A1–A5) + 4-homogeneity. Also carries
  this session's doc cleanup (README, `docs/STATUS_HISTORY.md`). **Awaiting merge to `main`.**
  Design: `planning/route-A-weak-coupling-plan.md`. (Supersedes the old axiom
  `torus_weakCoupling_lattice_connectedFourPoint_strictNeg`, which it does not use.)

## Dormant / superseded branches

- **`l5-affine-bound`** — the lattice u₄ engine (`lattice_u4_neg_uniform`, L5/L6F). Its key result is
  already on `main` and is **subsumed by Route A** (`route-a-weak-coupling` branched off it). Retire
  after PR #48 merges.
- **`option-b-feynman-kac`** (143 behind `main`) — **SUPERSEDED.** An early "B1–B5 slice transfer"
  framing of axiom 3; `main` has the more-advanced `Asym*` transfer files. Its plan
  `docs/transfer-instantiation-plan.md` is bannered superseded. Do not resume here.
- **`k-leaf-l3`, `k-leaf-l2-notes`** — stale u₄ side branches, subsumed. Retire.

## Other open threads (not branches)

- **Route B** (the `λ=1`/large-mass *normalization* of non-Gaussianity, via continuum dilation) —
  **DEFERRED**, sound but entangled with unbuilt clustering. `planning/continuum-rescaling-plan.md`.
- **Coherence keystone** (item 18) — conjoining `u₄≠0` with the *same* full-OS measure; weak-coupling
  uniqueness. `planning/coherence-analysis.md`.

## Deleted 2026-06-07 (were fully merged into main)

`codex/export-b2-modules`, `hs-trace-bridge` (PR #38), `upgrade/v4.30.0`.
