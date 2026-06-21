# Vetting — `nelson_exponential_estimate_master_bounded`

`Pphi2/NelsonEstimate/PolynomialChaosBridge.lean:1321`. INDEX item 12.

```yaml
---
axiom: nelson_exponential_estimate_master_bounded
file: Pphi2/NelsonEstimate/PolynomialChaosBridge.lean:1321
statement_hash: null
model: gemini
tool: mcp__gemini__deep_think_gemini
source_code: DT, LP
date: 2026-05-10 (rev 2 plan)
questions: [large-a-regime, hypercontractivity-bridge]
verdict: SATISFIABLE
rating: Likely correct
discharged: false
superseded_by: null
---
```

**Statement form** (informal): the Nelson hypercontractivity /
polynomial-chaos exponential estimate — the analytic engine under Layer A.

**Vetting source.** Recorded in [`AXIOM_AUDIT.md`](../../AXIOM_AUDIT.md)
under the `polynomial_chaos_exp_moment_bridge` entry:

> Over-stated to `∀ a > 0` (textbook GJ Ch. 8 covers `a ≤ 1`). Left as-is
> for downstream convenience; docstring "Note on strength" flags the
> over-statement. **Discharge plan**:
> [`polynomial-chaos-exp-moment-bridge-proof-plan.md`](../../docs/polynomial-chaos-exp-moment-bridge-proof-plan.md)
> (~2-3 weeks total, 5 phases).
>
> **DT verdict**: likely true (large-`a` regime trivial, integral → 1;
> combine with GJ small-`a` bound via `K = max(K_small, K_large)`).

**Conditions / follow-ups:**

- Sub-discharge plans:
  [`docs/nelson-bridge-generalization-plan.md`](../../docs/nelson-bridge-generalization-plan.md),
  [`docs/degree-piecewise-tail-discharge-plan.md`](../../docs/degree-piecewise-tail-discharge-plan.md),
  [`docs/polynomial-chaos-exp-moment-bridge-proof-plan.md`](../../docs/polynomial-chaos-exp-moment-bridge-proof-plan.md).
- Step 1 sub-discharge of the bridge axiom — `rough_error_variance` — is
  now fully theorem-derived (`#print axioms` shows only the Lean kernel).

**Cross-references:**

- Status: [`../../planning/INDEX.md`](../../planning/INDEX.md) item 12.
- Plans: see above.
