# Vetting — `pphi2_nontriviality`

`Pphi2/Main.lean:128`. INDEX item 11.

```yaml
---
axiom: pphi2_nontriviality
file: Pphi2/Main.lean:128
statement_hash: null
model: gemini + self-audit
tool: mcp__gemini__deep_think_gemini
source_code: DT, SA
date: 2026-06-04
questions: [statement-faithfulness, free-vs-interacting]
verdict: NEEDS_REVISION (mis-formulated; reformulated on T²)
rating: Needs review
discharged: partial (T² version proved; ℝ² version stands)
superseded_by: null
---
```

**Statement form** (informal): `S₂(f, f) > 0` for `f ≠ 0` — the
continuum-limit two-point function is nondegenerate.

**Vetting source.** [`planning/coherence-analysis.md`](../../planning/coherence-analysis.md),
[`planning/non-triviality.md`](../../planning/non-triviality.md), and the
2026-06-04 INDEX triage.

**Verdict (2026-06-04 triage):** **MIS-FORMULATED → reformulated on T².**

> The ℝ² axiom is `∃μ, S₂ > 0` with **P, mass unused** → free-field / δ₀
> satisfy it (`IsPphi2Limit` itself is δ₀-vacuous; see memory
> `pphi2-existence-vacuous-delta0`). **Honest version formulated on the
> genuine (axiom-clean-existing) T² theory**: `TorusNontriviality.lean` —
> `IsTorusPphi2Limit` + `torusPphi2Limit_exists` (PROVED),
> `TorusIsNondegenerate` (S₂ > 0).
>
> ⚠️ Route **corrected** (Gemini-vetted, memory `pphi2-s2-domination-direction`):
> "Griffiths/FKG ⟹ ≥ free" is **wrong-direction** — continuum nondegeneracy
> needs short-distance singularity / cluster expansion (★★★), not FKG.

**Status (2026-06-04 triage):**

> **Actionable cheaply, but a project-intent decision.** Step 1 (free
> positivity) is **PROVED**: `gaussianContinuumLimit_nontrivial`
> (`GaussianLimit.lean:102`) exhibits a free-field continuum-limit measure
> with `∀ f ≠ 0, S₂(f, f) > 0` — which **already witnesses the axiom as
> literally stated** (`∃ μ, …`). So the axiom is dischargeable NOW via
> the free field. BUT that conflicts with intent (coherence Gap A: we
> want S₂ > 0 for the *interacting* μ). The genuine route is **missing**
> — FKG infra exists but is not applied to two-point monotonicity-in-coupling;
> pphi2's Nelson bound is an *upper* bound (wrong direction).

**Conditions / follow-ups:**

- **Human decision required:** cheap free-field discharge vs. keep open
  for the interacting result.
- T² version is proved (`TorusIsNondegenerate`); ℝ² version still stands.

**Cross-references:**

- Status: [`../../planning/INDEX.md`](../../planning/INDEX.md) item 11.
- Plans: [`../../planning/non-triviality.md`](../../planning/non-triviality.md),
  [`../../planning/coherence-analysis.md`](../../planning/coherence-analysis.md).
