# Vetting — `asymGroundStateRep_eq_groundIsometry_one`

```yaml
---
axiom: asymGroundStateRep_eq_groundIsometry_one
file: Pphi2/AsymTorus/AsymBridgeInstance.lean:140
statement_hash: null
model: codex implementation audit
tool: local Lean build + upstream GroundMeasure API review
source_code: DT
date: 2026-06-23
questions: [typing, representative-bookkeeping, discharge]
verdict: SATISFIABLE
rating: Routine `Lp` representative bookkeeping
discharged: false
superseded_by: null
---
```

**Statement form.** The upstream ground isometry sends the constant-one vector
in `L²(Ω² dν)` to the selected `L²(ν)` asym ground vector.

**Why it is expected.** `groundIsometry_coeFn` represents `W f` by
`mk(f) * Ω`; for `f = 1`, this is `Ω` a.e. The selected `Ω` representative is
definitionally the `AEStronglyMeasurable.mk` representative of
`asymGroundVector`.

**Discharge plan.** Prove an `Lp.ext` lemma using `groundIsometry_coeFn`,
`Lp.coeFn_const`, and `asymGroundVector_coeFn_eq_groundStateRep`.
