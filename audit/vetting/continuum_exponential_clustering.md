# Vetting — `continuum_exponential_clustering`

`Pphi2/ContinuumLimit/AxiomInheritance.lean:354`. INDEX item 8.

```yaml
---
axiom: continuum_exponential_clustering
file: Pphi2/ContinuumLimit/AxiomInheritance.lean:354
statement_hash: null
model: gemini
tool: mcp__gemini__deep_think_gemini
source_code: DT, SA
date: 2026-02-23
questions: [pass-clustering-to-limit]
verdict: SATISFIABLE
rating: Standard
discharged: false
superseded_by: null
---
```

**Statement form** (informal): clustering passes from the lattice to
the continuum measure (Lt-uniform exponential clustering).

**Vetting source.** [`docs/cyl-2-scope.md`](../../docs/cyl-2-scope.md).

**Verdict:** Standard — once items 14/15 (the lattice clustering inputs)
land, this is a pass-to-the-limit step.

**Conditions / follow-ups:**

- Depends on items 14 + 15 (`two_point_clustering_from_spectral_gap`,
  `general_clustering_from_spectral_gap`) — both currently scoped, riding
  on the proved B2 trace bridge once it lands.
- Currently load-bearing for `pphi2_existence` (one of the 4 project
  axioms appearing in the kernel certificate).

**Cross-references:**

- Status: [`../../planning/INDEX.md`](../../planning/INDEX.md) item 8.
- Plan: [`../../docs/cyl-2-scope.md`](../../docs/cyl-2-scope.md).
