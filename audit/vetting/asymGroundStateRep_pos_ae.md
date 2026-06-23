# Vetting — `asymGroundStateRep_pos_ae`

```yaml
---
axiom: asymGroundStateRep_pos_ae
file: Pphi2/AsymTorus/AsymBridgeInstance.lean:81
statement_hash: null
model: codex implementation audit
tool: local Lean build + Route-A plan review
source_code: DT, LP
date: 2026-06-23
questions: [typing, strength, non-vacuity, discharge]
verdict: SATISFIABLE
rating: Standard representative-normalization obligation
discharged: false
superseded_by: null
---
```

**Statement form.** The measurable `AEStronglyMeasurable.mk` representative of
the selected asym Jentzsch ground vector is strictly positive `volume`-a.e.

**Why it is expected.** The generic Jentzsch proof already gives constant sign
for top eigenvectors of positivity-improving compact self-adjoint transfer
operators. The pphi2 wrapper currently selects a Hilbert-basis ground vector
but does not store the sign-normalization proof for that chosen representative.

**Discharge plan.** Refine `asymTransferGroundExcitedData` or add a signed
ground-vector wrapper so the distinguished basis vector is replaced by its
positive representative, then transport the existing Jentzsch constant-sign
lemma through `AEStronglyMeasurable.mk`.
