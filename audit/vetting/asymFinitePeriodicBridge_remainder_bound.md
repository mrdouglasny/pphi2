# Vetting — `asymFinitePeriodicBridge_remainder_bound`

```yaml
---
axiom: asymFinitePeriodicBridge_remainder_bound
file: Pphi2/AsymTorus/AsymBridgeInstance.lean:174
statement_hash: null
model: codex implementation audit
tool: local Lean build + Layer-B2 Route-A plan review
source_code: DT, LP
date: 2026-06-23
questions: [typing, strength, discharge]
verdict: SATISFIABLE
rating: Main finite-periodic analytic remainder obligation
discharged: false
superseded_by: null
---
```

**Statement form.** After removing the two one-perp GNS legs from the
finite-periodic connected path two-point function, the remaining scalar
residual is bounded by `C_rem * γ^n`.

**Why it is expected.** This is precisely the model-specific hypothesis the
upstream bridge leaves to concrete transfer kernels. It packages the `R*R`
signed-kernel term, denominator correction, and finite-volume one-point
corrections.

**Discharge plan.** Prove Hilbert-Schmidt or direct kernel-integral bounds for
the explicit Gaussian asym transfer kernel remainder, using the proved
operator-norm decay bricks in `AsymTraceBridge.lean` and the kernel-power
dictionary in `AsymTransferKernelOperator.lean`.
