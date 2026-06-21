# Vetting — `continuumLimit_nonGaussian`

`Pphi2/ContinuumLimit/Convergence.lean:256`. INDEX item 9.

```yaml
---
axiom: continuumLimit_nonGaussian
file: Pphi2/ContinuumLimit/Convergence.lean:256
statement_hash: null
model: gemini + codex (Route A vetting)
tool: mcp__gemini__deep_think_gemini
source_code: DT, LP
date: 2026-06-07 (Route A vetting on PR #48)
questions: [non-Gaussianity-route, weak-coupling-scope]
verdict: SATISFIABLE
rating: Likely correct
discharged: false
partial_discharge: "T² content axiom-free on PR #48 (route-a-weak-coupling, OPEN); ℝ² lift still open. Not yet on this branch."
superseded_by: null
---
```

**Statement form** (informal): `u₄ ≠ 0` for the continuum-limit measure
— the limit is genuinely interacting (non-Gaussian).

**Vetting source.** `planning/route-A-weak-coupling-plan.md` (on branch
`route-a-weak-coupling`, not yet merged — PR #48),
[`planning/non-triviality.md`](../../planning/non-triviality.md), and
the [`AXIOM_AUDIT.md`](../../AXIOM_AUDIT.md) Route A entry.

**Status (2026-06-07):** **T² non-Gaussianity content is proved
AXIOM-FREE via Route A on PR #48 (branch `route-a-weak-coupling`, currently
OPEN — not on this branch / not on `main`):**

> `torus_pphi2_isInteractingStrict_weakCoupling`
> (`TorusContinuumLimit/TorusCouplingResult.lean`, on `route-a-weak-coupling`)
> is a THEOREM with `#print axioms ⟹ [propext, Classical.choice, Quot.sound]`:
> for some small coupling `g₀ ∈ (0, 1]`, the continuum limit of the
> coupling-`g₀` interacting torus measures has
> `torusConnectedFourPoint μ (torusOne) < 0` (`TorusIsInteractingStrict`,
> hence `TorusIsInteracting`). PR #48.

**The ℝ² (infinite-volume) `continuumLimit_nonGaussian` axiom itself
remains** on `main` and on this branch — the T² → ℝ² lift requires
`L → ∞` cluster expansion. The Route-A T² result is a prerequisite for,
not a replacement of, the ℝ² axiom.

**Conditions / follow-ups:**

- Still open: (i) the conventional `λ = 1` / large-mass *normalization* —
  Route B (continuum dilation), DEFERRED, needs clustering
  ([`planning/continuum-rescaling-plan.md`](../../planning/continuum-rescaling-plan.md));
  (ii) the **ℝ²** axiom itself (T² → ℝ² lift); (iii) conjoining `u₄ ≠ 0`
  with the *same* OS measure + full OS0–OS4 (keystone 18).

**Cross-references:**

- Status: [`../../planning/INDEX.md`](../../planning/INDEX.md) item 9.
- Plans: [`../../planning/non-triviality.md`](../../planning/non-triviality.md),
  `planning/route-A-weak-coupling-plan.md` (on PR #48 / branch
  `route-a-weak-coupling`).
