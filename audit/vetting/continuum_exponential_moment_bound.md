# Vetting — `continuum_exponential_moment_bound`

`Pphi2/ContinuumLimit/AxiomInheritance.lean:123`. INDEX item 6.

```yaml
---
axiom: continuum_exponential_moment_bound
file: Pphi2/ContinuumLimit/AxiomInheritance.lean:123
statement_hash: null
model: gemini
tool: mcp__gemini__deep_think_gemini
source_code: DT, LP
date: 2026-02-23
questions: [pass-to-limit-of-uniform-bound]
verdict: SATISFIABLE
rating: Standard
discharged: false
superseded_by: null
---
```

**Statement form** (informal): the `Lt`-uniform interacting exponential-moment
bound (item 1) passes to the continuum-limit measure.

**Vetting source.** Standard pass-to-the-limit reasoning; the input bound
(item 1) is the deep content. Plan:
[`docs/asym-interacting-expmoment-volume-uniform-discharge-plan.md`](../../docs/asym-interacting-expmoment-volume-uniform-discharge-plan.md).

**Verdict:** Standard — once item 1 is in hand and the continuum limit
machinery is wired, this is a Fatou/weak-convergence step.

**Conditions / follow-ups:**

- Depends on item 1 (`asymInteracting_expMoment_volume_uniform`).
- The cylinder version `cylinderIR_uniform_exponential_moment` is already
  proved.

**Cross-references:**

- Status: [`../../planning/INDEX.md`](../../planning/INDEX.md) item 6.
- Plan: [`../../docs/asym-interacting-expmoment-volume-uniform-discharge-plan.md`](../../docs/asym-interacting-expmoment-volume-uniform-discharge-plan.md).
