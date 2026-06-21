# Vetting — `os2_from_phi4`

`Pphi2/Bridge.lean:345`. INDEX item 5.

```yaml
---
axiom: os2_from_phi4
file: Pphi2/Bridge.lean:345
statement_hash: null
model: gemini (early audit) + self-audit
tool: mcp__gemini__deep_think_gemini
source_code: DT, SA
date: 2026-02-23
questions: [OS2-route-via-rotation-defect]
verdict: SATISFIABLE
rating: Likely correct
discharged: false
superseded_by: null
---
```

**Statement form** (informal): OS2 (E(2)-invariance) for the φ⁴ measure
follows from the rotation defect bound (`rotation_cf_defect_polylog_bound`).

**Vetting source.** [`docs/axiom_proof_plans.md`](../../docs/axiom_proof_plans.md)
and the rotation-restoration thread.

**Verdict:** Likely correct — standard "polylog defect ⟹ continuum
E(2)-invariance" passage. The depth is in the input axiom (item 13,
`rotation_cf_defect_polylog_bound`), not here.

**Conditions / follow-ups:**

- Depends on item 13 being discharged first.
- Re-vet if the input axiom's quantifier structure changes.

**Cross-references:**

- Status: [`../../planning/INDEX.md`](../../planning/INDEX.md) item 5.
- Plan: [`../../docs/axiom_proof_plans.md`](../../docs/axiom_proof_plans.md),
  [`../../docs/cylinder-master-plan.md`](../../docs/cylinder-master-plan.md).
- Input axiom: [`rotation_cf_defect_polylog_bound.md`](rotation_cf_defect_polylog_bound.md).
