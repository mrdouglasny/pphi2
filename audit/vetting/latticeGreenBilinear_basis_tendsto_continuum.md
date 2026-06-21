# Vetting — `latticeGreenBilinear_basis_tendsto_continuum`

`Pphi2/GaussianContinuumLimit/PropagatorConvergence.lean:103`. INDEX item 10.

```yaml
---
axiom: latticeGreenBilinear_basis_tendsto_continuum
file: Pphi2/GaussianContinuumLimit/PropagatorConvergence.lean:103
statement_hash: null
model: gemini
tool: mcp__gemini__deep_think_gemini
source_code: DT, LP
date: 2026-02-23
questions: [free-propagator-limit, basis-convergence]
verdict: SATISFIABLE
rating: Standard
discharged: false
superseded_by: null
---
```

**Statement form** (informal): free propagator (bilinear form) lattice → continuum
on a basis.

**Vetting source.** [`docs/pr10_summary.md`](../../docs/pr10_summary.md).

**Verdict:** Standard (free/Gaussian content — the most tractable input in
its cluster). The proved sibling `second_moment_asym_tendsto` is the
torus → torus case; this axiom needs the additional IR-limit `L → ∞`
torus box → flat ℝ² Fourier Green.

**Conditions / follow-ups (from [`planning/INDEX.md`](../../planning/INDEX.md) 2026-06-04 triage):**

- **BLOCKED on an IR-limit theorem.** The proved sibling
  `lattice_green_tendsto_continuum_asym` is **torus → torus only**.
  Missing:
  `ir_limit_continuum_green_tendsto : limₗ asymTorusContinuumGreen L = continuumGreenBilinear`.
- Then dominated convergence + DM nuclear extension finishes.
- **Not on the T² critical path** (~3 wk standalone).

**Cross-references:**

- Status: [`../../planning/INDEX.md`](../../planning/INDEX.md) item 10.
- Plan: [`../../docs/pr10_summary.md`](../../docs/pr10_summary.md).
