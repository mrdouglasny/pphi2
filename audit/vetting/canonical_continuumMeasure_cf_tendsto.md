# Vetting — `canonical_continuumMeasure_cf_tendsto`

`Pphi2/ContinuumLimit/AxiomInheritance.lean:327`. INDEX item 7.

```yaml
---
axiom: canonical_continuumMeasure_cf_tendsto
file: Pphi2/ContinuumLimit/AxiomInheritance.lean:327
statement_hash: null
model: gemini
tool: mcp__gemini__deep_think_gemini
source_code: DT, SA
date: 2026-02-23
questions: [self-existential-form, lattice-realization]
verdict: NEEDS_REVISION
rating: Needs review (statement form questioned)
discharged: false
superseded_by: null
---
```

**Statement form** (informal): characteristic-function convergence of the
canonical lattice measures to the continuum limit, with `a_n → 0` and
`(N n : ℝ) * a n → ∞`.

**Vetting source.** [`docs/pr10_summary.md`](../../docs/pr10_summary.md) +
[`planning/INDEX.md`](../../planning/INDEX.md) 2026-06-04 triage.

**Verdict (2026-06-04 triage):** **BLOCKED + needs-human.** Statement is
sound in form (already couples `N → ∞` and `N · a → ∞`), but the proof
needs a non-standard **lattice-realization** lemma: *any* `IsPphi2Limit`
measure is the weak limit of canonically-coupled `continuumMeasure`s
(a converse to the continuum limit — unusual; QFT texts only prove
lattice → continuum). The axiom's self-existential `(N, a)` is decoupled
from the abstract limit witness — **review whether the axiom should
instead be a direct weak-convergence statement** before discharging.

**Conditions / follow-ups:**

- **Statement re-review needed** before formalizing the discharge.
- Currently load-bearing for `pphi2_existence` (one of the 4 project
  axioms appearing in the kernel certificate).

**Cross-references:**

- Status: [`../../planning/INDEX.md`](../../planning/INDEX.md) item 7.
- Plan: [`../../docs/pr10_summary.md`](../../docs/pr10_summary.md).
- Kernel trace: [`../axiom-report.txt`](../axiom-report.txt) — listed under `pphi2_existence`.
