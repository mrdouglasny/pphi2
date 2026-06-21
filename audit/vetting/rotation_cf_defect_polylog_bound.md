# Vetting — `rotation_cf_defect_polylog_bound`

`Pphi2/OSProofs/OS2_WardIdentity.lean:614`. INDEX item 13.

```yaml
---
axiom: rotation_cf_defect_polylog_bound
file: Pphi2/OSProofs/OS2_WardIdentity.lean:614
statement_hash: null
model: gemini
tool: mcp__gemini__deep_think_gemini
source_code: DT, LP
date: 2026-02-23
questions: [polylog-vs-linear, scaling]
verdict: SATISFIABLE
rating: Likely correct
discharged: false
superseded_by: null
---
```

**Statement form** (informal): the lattice characteristic-function rotation
defect tends to zero in the continuum limit with a polynomial-log bound,
`|rotationCFDefect| ≤ C · a² · (1 + |log a|)^m`.

**Vetting source.** The rotation-restoration / anomaly-bound thread.
Plan: [`docs/dual-construction-strategy.md`](../../docs/dual-construction-strategy.md),
[`docs/cylinder-master-plan.md`](../../docs/cylinder-master-plan.md).
Anomaly bound reference per memory note: Glimm-Jaffe Thm 19.3.1 — the
rotation anomaly is `O(a² |log a|^p)`, **NOT** pure `O(a²)` (super-
renormalizability limits the log power but doesn't eliminate it).

**Verdict:** Likely correct with the polynomial-log strengthening.

**Conditions / follow-ups:**

- `tendsto_zero_pow_mul_one_add_abs_log_pow` (the analytic prerequisite
  for arbitrary `m ≥ 1`) is **PROVED**.
- The pointwise observable API `rotationCFPointwiseDefect` is a proved
  support layer.
- Currently load-bearing for `pphi2_existence` (one of the 4 project
  axioms in the kernel certificate).

**Cross-references:**

- Status: [`../../planning/INDEX.md`](../../planning/INDEX.md) item 13.
- Plans: [`../../docs/dual-construction-strategy.md`](../../docs/dual-construction-strategy.md),
  [`../../docs/cylinder-master-plan.md`](../../docs/cylinder-master-plan.md).
- Consumer: [`os2_from_phi4.md`](os2_from_phi4.md) (item 5).
