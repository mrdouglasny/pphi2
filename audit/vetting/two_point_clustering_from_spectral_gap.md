# Vetting — `two_point_clustering_from_spectral_gap`

`Pphi2/OSProofs/OS4_MassGap.lean:137`. INDEX item 14.

```yaml
---
axiom: two_point_clustering_from_spectral_gap
file: Pphi2/OSProofs/OS4_MassGap.lean:137
statement_hash: null
model: gemini
tool: mcp__gemini__deep_think_gemini
source_code: DT, LP, SA
date: 2026-06-04
questions: [reduces-to-proved-bridge, square-vs-asym]
verdict: SATISFIABLE
rating: Likely correct (★★ given B2 trace bridge)
discharged: false
superseded_by: null
---
```

**Statement form** (informal): the two-point function exhibits exponential
clustering at rate `γ = exp(−massGap · a)` — the OS4 mass-gap content
for two-point.

**Vetting source.** [`planning/cyl-2a-spectral-gap.md`](../../planning/cyl-2a-spectral-gap.md)
and the 2026-06-04 INDEX triage.

**Verdict (2026-06-04 triage):**

> = `connected_two_point_le` with `γ = e^{−massGap · a}` via
> `twoPoint_dictionary` + `asymTransferKernel_kPow_apply` (proved).
> Do in the B2 trace-bridge PR.

**Reassessment (2026-06-04 triage, INDEX clustering 14/15 section):**

> The B2 dictionary (`twoPoint_dictionary`) exists **only on the asym torus**;
> 14/15 are stated on the **square** `FinLatticeField 2 Ns`. The square lattice
> has transfer infra (`Pphi2/TransferMatrix/*`) but **no square
> `twoPoint_dictionary` and no square `GappedTransfer` packaging**.
> So 14/15 are BLOCKED on **building the square trace dictionary**
> (port the asym B2/B4 chain to the square, or prove asym↔square at `Nt=Ns`).

**Conditions / follow-ups:**

- Depends on: square trace dictionary (port the asym B2/B4 chain) +
  item 17 (`spectral_gap_uniform`).

**Cross-references:**

- Status: [`../../planning/INDEX.md`](../../planning/INDEX.md) item 14.
- Plan: [`../../planning/cyl-2a-spectral-gap.md`](../../planning/cyl-2a-spectral-gap.md),
  [`../../docs/cyl-2-scope.md`](../../docs/cyl-2-scope.md).
