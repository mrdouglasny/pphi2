# Vetting — `asymTorusInteracting_exponentialMomentBound`

`Pphi2/AsymTorus/AsymTorusOS.lean:852` (**private** scaffolding axiom).

```yaml
---
axiom: asymTorusInteracting_exponentialMomentBound
file: Pphi2/AsymTorus/AsymTorusOS.lean:852
visibility: private
statement_hash: null
model: self-audit (scaffolding)
tool: n/a
source_code: SA
date: 2026-02-23
questions: [scaffolding-only]
verdict: SATISFIABLE
rating: Standard (scaffolding consumed only inside AsymTorusOS)
discharged: false
superseded_by: null
---
```

**Statement form** (informal): torus-side interacting exponential-moment
bound; private scaffolding consumed only inside `AsymTorusOS.lean`.

**Vetting source.** Discharge plan in
[`docs/asym-interacting-expmoment-volume-uniform-discharge-plan.md`](../../docs/asym-interacting-expmoment-volume-uniform-discharge-plan.md);
status pinned in [`README.md`](../../README.md) per-route discussion.

**Verdict:** Standard scaffolding. The deeper content lives in the public
axiom item 1 (`asymInteracting_expMoment_volume_uniform`); this private
axiom is a torus-side packaging.

**Conditions / follow-ups:**

- Discharge piggybacks on item 1's Layer-C assembly.
- Not architectural; not enumerated in `planning/INDEX.md`'s 17.

**Cross-references:**

- Related: [`asymInteracting_expMoment_volume_uniform.md`](asymInteracting_expMoment_volume_uniform.md).
