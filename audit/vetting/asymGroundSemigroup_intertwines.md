# Vetting — `asymGroundSemigroup_intertwines`

```yaml
---
axiom: asymGroundSemigroup_intertwines
file: Pphi2/AsymTorus/AsymBridgeInstance.lean:219
statement_hash: null
model: codex implementation audit
tool: local Lean build + upstream GroundSemigroup/GroundGap API review
source_code: DT, LP
date: 2026-06-23
questions: [typing, strength, discharge]
verdict: SATISFIABLE
rating: Standard after ground-isometry unitarity upgrade
discharged: false
superseded_by: null
---
```

**Statement form.** The adjoint-transport ground semigroup packaged by
`GroundSemigroupData` intertwines with the normalized asym transfer through
`groundIsometry`.

**Why it is expected.** In the usual Doob/GNS transform, `U_t = W^{-1} T^t W`,
so `W U_t = T^t W`. The current upstream construction uses the adjoint
`W†`; the equation follows once `Ω > 0` a.e. upgrades `W` from an isometric
embedding to a unitary equivalence.

**Discharge plan.** Prove the upstream ground-isometry surjectivity/unitarity
lemma from `Ω_pos_ae`, then replace the adjoint with the inverse in the
definition of `groundSemigroup`.
