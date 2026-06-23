# Vetting — `asymTransferNormalized_contract`

```yaml
---
axiom: asymTransferNormalized_contract
file: Pphi2/AsymTorus/AsymBridgeInstance.lean:128
statement_hash: null
model: codex implementation audit
tool: local Lean build + spectral-gap code review
source_code: DT, LP
date: 2026-06-23
questions: [typing, strength, non-vacuity, discharge]
verdict: SATISFIABLE
rating: Standard compact self-adjoint spectral-radius consequence
discharged: false
superseded_by: null
---
```

**Statement form.** The transfer operator normalized by the top eigenvalue
`λ₀` is a contraction on all of `L²(volume)`.

**Why it is expected.** pphi2 proves compactness, self-adjointness,
positivity-improving Perron-Frobenius data, and a strict contraction on the
vacuum-orthogonal complement. The global contraction follows from the same
spectral decomposition: the top eigenspace has normalized eigenvalue `1`, and
the remaining spectrum has absolute value at most `1`.

**Discharge plan.** Reuse the Hilbert-basis spectral package in
`AsymSpectralGap.lean` to decompose an arbitrary vector into the ground
component plus the orthogonal component, then combine `T Ω = Ω` with the
proved orthogonal contraction.
