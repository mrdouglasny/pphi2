# Branch & thread map — where the live work is

Concise navigational map of pphi2's in-flight branches and the axiom each targets.
For the full per-axiom status machine see [`planning/INDEX.md`](planning/INDEX.md); for the
axiom inventory see [`docs/AXIOM_STATUS.md`](docs/AXIOM_STATUS.md).

> **Re-read this before resuming after a break.** It exists because on 2026-06-07 two inherited
> directives — a compaction summary and a `plan-loop` — were *both* found chasing **superseded**
> branches (the continuum-rescaling docs route and `option-b-feynman-kac`), while the actual live
> code frontier was elsewhere. Check this map before trusting a hand-off about "the current task".

## Trunk

- **`main`** — canonical. Holds the most-advanced state of *both* live discharge efforts:
  - **Axiom 3** `asymInteractingVariance_le_freeVariance_Lt_uniform` (Layer-B2 / transfer route):
    B2 trace-bridge bricks 0–2 + B5a proved on main; remaining = the Hilbert–Schmidt trace-bridge
    tail + B5b single-slice stability. Current plan = [`docs/B4B5-design.md`] + INDEX item 3.
  - **Axiom 9** `torus_weakCoupling_lattice_connectedFourPoint_strictNeg` (u₄ non-triviality):
    scaffolding (step-IV moment convergence, field redefinition, free-field `u₄=0` anchor) proved &
    axiom-clean on main; the perturbative discharge itself is in progress on `l5-affine-bound`.

## Live feature branches

- **`l5-affine-bound`** (24 ahead / 3 behind main) — **the live frontier for axiom 9 (u₄), lattice
  route.** L5 complete (`lattice_u4_neg_uniform` = weak-coupling lattice `u₄(g₀) < 0`, uniform in N),
  L6F reduction (`torusConnectedFourPoint = u4(g=1)`), pointwise covariance bound
  `|C(x,y)| ≤ (a^d)⁻¹·mass⁻²`. The axiom is **not yet discharged** — the open endgame is the
  large-mass = weak-coupling step (see commit `203ce5f`, "direct large-mass, not field redefinition").
  Plans: `planning/L5-plan.md`, `planning/L6F-mass-coupling-plan.md`.
- **`k-leaf-l3`** (7 ahead / 4 behind) — u₄ L3 + L5 planning docs; largely subsumed by
  `l5-affine-bound`. Fold its unique docs into l5/main, then retire.

## Dormant / superseded branches

- **`option-b-feynman-kac`** (4 ahead / **141 behind main**) — **SUPERSEDED. Do not resume here.**
  An early "B1–B5 slice transfer matrix" framing of axiom 3; `main` has since built its own
  `Pphi2/AsymTorus/AsymTransferInstantiation.lean` + the advanced Layer-B2 route
  (`AsymEnergyFactorization`, `AsymMeasureFactorization`, `AsymVarianceDischarge`), discarding this
  branch's `asymSliceEquiv` (B1a) prototype. Its plan `docs/transfer-instantiation-plan.md` is stale
  (banner added at its top). Kept (not merged) only as a record of the discarded prototype.
- **`k-leaf-l2-notes`** (1 ahead / 6 behind) — a single stale notes commit. Retire.

## Deleted 2026-06-07 (were fully merged into main)

`codex/export-b2-modules`, `hs-trace-bridge` (PR #38), `upgrade/v4.30.0`.

## The two routes to axiom 9 (u₄) — these compete; pick one

1. **Lattice route (LIVE, has code)** — `l5-affine-bound`: affine `u₄''` bound ⟹ lattice `u₄(g₀) < 0`;
   discharge via large-mass = weak-coupling. The grinding effort with real Lean.
2. **Continuum-rescaling route (PROPOSED, docs-only)** — `planning/continuum-rescaling-plan.md` (main):
   prove the continuum family + 2D scale-covariance equivalence, transport weak-coupling `u₄ < 0` to
   the physical point. Gemini-vetted SOUND but **not started**. An *alternative* to route 1, not a
   complement — don't run both.
