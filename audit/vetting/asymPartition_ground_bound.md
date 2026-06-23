# Vetting — `asymPartition_ground_bound`

```yaml
---
axiom: asymPartition_ground_bound
file: Pphi2/AsymTorus/AsymBridgeInstance.lean:159
statement_hash: null
model: codex implementation audit
tool: local Lean build + transfer trace dictionary review
source_code: DT, LP
date: 2026-06-23
questions: [typing, positivity, discharge]
verdict: SATISFIABLE
rating: Standard positive-trace lower bound
discharged: false
superseded_by: null
---
```

**Statement form.** The finite-periodic path partition function is at least
`λ₀^n`, the top-eigenvalue contribution of the transfer power.

**Why it is expected.** For a positive compact transfer operator,
`partition n` is the trace/kernel diagonal integral of `T^n`. The positive
ground-state eigenvector contributes exactly `λ₀^n`, and the remaining
positive spectral contributions cannot decrease the trace.

**Discharge plan.** Connect `TransferSystem.partition` to the trace of
`asymTransferOperatorCLM ^ n` through the existing kernel-power dictionary,
then evaluate the ground projection contribution using
`asymTransferOperatorCLM_pow_groundVector`.
