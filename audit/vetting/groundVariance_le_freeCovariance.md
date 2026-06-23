# Vetting — `groundVariance_le_freeCovariance`

```yaml
---
axiom: groundVariance_le_freeCovariance
file: Pphi2/AsymTorus/AsymB5bSingleSlice.lean
statement_hash: null
model: codex implementation audit
tool: local Lean build + Layer-B2 Route-A a-power review
source_code: CX, LP
date: 2026-06-23
questions: [single-slice-stability, a-power-bookkeeping, discharge]
verdict: SATISFIABLE PENDING EXTERNAL VETTING
rating: Narrow B5b analytic input
discharged: false
superseded_by: null
---
```

**Statement form.** At fixed spatial circumference `Ls`, the ground-state
single-slice second moment
`∫ <g,ψ>² Ω(ψ)² dν` is bounded by a constant times the one-slice free
GJ covariance, uniformly in `a`, `Nt`, and the time slice.

**Why this is the right formal target.** The RHS is expressed using
`latticeCovarianceAsymGJ` after a one-slice lift, not by replacing the
covariance factorization operator with an informal `Q⁻¹`. This preserves the
crux-2 square-root convention: `latticeCovarianceAsymGJ` carries the `a⁻¹`
GJ normalization, and scaling a slice vector as `g_t = a • δ_site` contributes
exactly `a²` (`freeSingleSliceCovariance_smul`).

**Discharge plan.** Specialize the existing Nelson/chessboard estimate
(`asymNelson_exponential_estimate_iso`) to the `Ls`-fixed single-time-slice
ground-state measure. Before removing the axiom, re-vet the derivation of the
spatial free covariance identification and explicitly test the `a • δ_site`
case against the formal scaling lemma.

**Assembly note.** `AsymB5bSingleSlice.lean` keeps the later conversion from
the sum of one-slice free covariances to the full spacetime free variance as an
explicit hypothesis (`hFreeAssemble`). This avoids the known false shortcut:
exposing a standalone `1 / (1 - γ)` factor gives an `a`-non-uniform bound.
