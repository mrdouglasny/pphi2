# Vetting — `schwinger_agreement`

`Pphi2/Bridge.lean:274`. INDEX item 4.

```yaml
---
axiom: schwinger_agreement
file: Pphi2/Bridge.lean:274
statement_hash: null
model: gemini (early audit) + self-audit
tool: mcp__gemini__deep_think_gemini
source_code: DT, SA
date: 2026-02-23
questions: [bridge-consistency, bookkeeping]
verdict: SATISFIABLE
rating: Standard (bookkeeping bridge)
discharged: false
superseded_by: null
---
```

**Statement form** (informal): the constructed Schwinger functions agree
with the measure moments — a bookkeeping bridge between the
`pphi2`-lattice and `Phi4`-continuum Schwinger sequences.

**Vetting source.** [`docs/axiom_proof_plans.md`](../../docs/axiom_proof_plans.md)
("Phase 6: Bridge" section) — assessed as a structural/bookkeeping axiom
rather than analytic content.

**Verdict:** Standard bookkeeping axiom that becomes a theorem once the
agreement between the lattice construction and the Phi4 continuum
construction is formalized.

**Conditions / follow-ups (per [`planning/INDEX.md`](../../planning/INDEX.md) 2026-06-04 triage):**

- **BLOCKED on keystone 18** (cluster expansion / weak-coupling uniqueness).
  The axiom = "pphi2-lattice and Phi4-continuum Schwinger sequences agree",
  which is exactly the interchange-of-limits the cluster expansion provides.
- Missing lemma: `schwinger_pphi2_eq_phi4_of_weak_coupling`.
- The `measure_determined_by_schwinger` wrapper is already a theorem
  (2026-06-02); only this agreement input is missing.

**Cross-references:**

- Status: [`../../planning/INDEX.md`](../../planning/INDEX.md) item 4.
- Plan: [`../../docs/axiom_proof_plans.md`](../../docs/axiom_proof_plans.md).
- Keystone dependency: `planning/coherence-analysis.md` (item 18).
