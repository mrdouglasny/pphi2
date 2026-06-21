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
date: 2026-06-07 (Route A landed)
questions: [non-Gaussianity-route, weak-coupling-scope]
verdict: SATISFIABLE (T² content axiom-free; ℝ² version still axiom)
rating: Likely correct
discharged: partial (T² done via Route A; ℝ² lift still open)
superseded_by: null
---
```

**Statement form** (informal): `u₄ ≠ 0` for the continuum-limit measure
— the limit is genuinely interacting (non-Gaussian).

**Vetting source.** [`planning/route-A-weak-coupling-plan.md`](../../planning/route-A-weak-coupling-plan.md),
[`planning/non-triviality.md`](../../planning/non-triviality.md), and
the [`AXIOM_AUDIT.md`](../../AXIOM_AUDIT.md) Route A entry.

**Status (2026-06-07):** **T² non-Gaussianity content is DONE,
AXIOM-FREE** via Route A:

> `torus_pphi2_isInteractingStrict_weakCoupling`
> (`TorusContinuumLimit/TorusCouplingResult.lean`) is a THEOREM with
> `#print axioms ⟹ [propext, Classical.choice, Quot.sound]`: for some
> small coupling `g₀ ∈ (0, 1]`, the continuum limit of the coupling-`g₀`
> interacting torus measures has `torusConnectedFourPoint μ (torusOne) < 0`
> (`TorusIsInteractingStrict`, hence `TorusIsInteracting`). PR #48.

**The ℝ² (infinite-volume) `continuumLimit_nonGaussian` axiom itself
remains** — the T² → ℝ² lift requires `L → ∞` cluster expansion.

**Conditions / follow-ups:**

- Still open: (i) the conventional `λ = 1` / large-mass *normalization* —
  Route B (continuum dilation), DEFERRED, needs clustering
  ([`planning/continuum-rescaling-plan.md`](../../planning/continuum-rescaling-plan.md));
  (ii) the **ℝ²** axiom itself (T² → ℝ² lift); (iii) conjoining `u₄ ≠ 0`
  with the *same* OS measure + full OS0–OS4 (keystone 18).

**Cross-references:**

- Status: [`../../planning/INDEX.md`](../../planning/INDEX.md) item 9.
- Plans: [`../../planning/non-triviality.md`](../../planning/non-triviality.md),
  [`../../planning/route-A-weak-coupling-plan.md`](../../planning/route-A-weak-coupling-plan.md).
