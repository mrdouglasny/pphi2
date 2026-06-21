# Vetting — `general_clustering_from_spectral_gap`

`Pphi2/OSProofs/OS4_MassGap.lean:160`. INDEX item 15.

```yaml
---
axiom: general_clustering_from_spectral_gap
file: Pphi2/OSProofs/OS4_MassGap.lean:160
statement_hash: null
model: gemini
tool: mcp__gemini__deep_think_gemini
source_code: DT, LP, SA
date: 2026-06-04
questions: [bounded-FG-lift]
verdict: SATISFIABLE
rating: Likely correct (★★ given B2 trace bridge)
discharged: false
superseded_by: null
---
```

**Statement form** (informal): bounded observables `F, G` exhibit
exponential clustering — the OS4 general clustering content.

**Vetting source.** Same chain as item 14
([`general_clustering_from_spectral_gap`]). Per
[`planning/INDEX.md`](../../planning/INDEX.md):

> Same [as item 14], bounded `F, G` → `M_F, M_G`.

**Conditions / follow-ups:**

- Same as item 14: depends on the square trace dictionary + item 17.

**Cross-references:**

- Status: [`../../planning/INDEX.md`](../../planning/INDEX.md) item 15.
- See [`two_point_clustering_from_spectral_gap.md`](two_point_clustering_from_spectral_gap.md).
