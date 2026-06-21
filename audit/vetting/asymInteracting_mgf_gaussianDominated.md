# Vetting — `asymInteracting_mgf_gaussianDominated`

Captured soundness-review records for `asymInteracting_mgf_gaussianDominated`
(`Pphi2/AsymTorus/AsymExpMomentDischarge.lean:127`). Linked from
[`../../AXIOM_AUDIT.md`](../../AXIOM_AUDIT.md) and
[`../../planning/INDEX.md`](../../planning/INDEX.md) item 2.

---

```yaml
---
axiom: asymInteracting_mgf_gaussianDominated
file: Pphi2/AsymTorus/AsymExpMomentDischarge.lean:127
statement_hash: null
model: gemini-3-pro
tool: mcp__gemini__deep_think_gemini
source_code: DT, LP
date: 2026-05-31
questions: [architecture-correctness, factorization, dependencies]
verdict: SATISFIABLE
rating: Likely correct
discharged: false
superseded_by: null
---
```

**Statement form** (informal): the MGF of `⟨ω, f⟩` under the asymmetric-torus
interacting measure is Gaussian-dominated — `MGF(t) ≤ exp(t² · Var(f) / 2)`
(possibly with a constant prefactor, `K = 2`).

**Layer A** of the Layer-C assembly for
`asymInteracting_expMoment_volume_uniform` (item 1). The Newman MGF
Gaussian-domination inequality, instantiated for the asym-lattice
interacting measure.

**Vetting source.**
[`docs/asym-expmoment-discharge-via-lee-yang-vet-request.md`](../../docs/asym-expmoment-discharge-via-lee-yang-vet-request.md)
— a structured deep-think vet of the Layer-A reduction architecture (the
factorization `(LY) := (LY1) + (LY2) + (LY3)` plus the Newman MGF
inequality).

**Verdict summary (2026-05-31):**

Architecture **CONFIRMED** as correct; four recalibrations applied:

1. `IsLeeYang` is **multivariate** with a projection lemma to univariate
   marginals (was univariate + multivariate-as-add-on).
2. `iteratedAsano` lives over `SimpleGraph V` with edge weighting, not
   specialized to rectangular lattices.
3. `evenPolynomialWick` takes an explicit variance parameter (was
   hardcoded unit variance).
4. Pphi2-side adapter scope bumped from ~50-150 lines to **~200-400
   lines** — the global covariance representation does NOT admit a
   one-step disintegration into the site-wise product measure that
   Griffiths-Simon consumes; the adapter needs density-vs-flat-Lebesgue
   rewriting + nearest-neighbour coupling extraction.

The four planned files (`Polynomial/RealZeros.lean`, `Polynomial/Asano.lean`,
`Measure/Newman.lean`, `Measure/GriffithsSimon.lean`) stand; their content
has been refined in [`lee-yang/PLAN.md`](https://github.com/mrdouglasny/lee-yang/blob/main/PLAN.md)
accordingly.

**Conditions / follow-ups:**

- **Discharge depends on the [`lee-yang`](https://github.com/mrdouglasny/lee-yang)
  repo.** Phase 1 polynomial side is **DONE, 0 sorries, 0 axioms** (Asano main
  lemma + iteratedAsano fold, as of 2026-06-02). `Measure/Newman.lean`
  (`IsLeeYang` + projection + Newman MGF inequality, the consumer-facing
  surface for this axiom) is the next deliverable; not started.
- **Re-vet if strengthened**: any change to the `K` constant or the
  variance functional form requires a fresh deep-think pass.

**Cross-references:**

- Live discharge plan: [`../../docs/asym-expmoment-discharge-via-lee-yang-vet-request.md`](../../docs/asym-expmoment-discharge-via-lee-yang-vet-request.md).
- Upstream repo: [`lee-yang`](https://github.com/mrdouglasny/lee-yang) (Phase 1 polynomial side done).
- Downstream: [`asymInteracting_expMoment_volume_uniform.md`](asymInteracting_expMoment_volume_uniform.md) (Layer-C assembly).
- Status: [`../../planning/INDEX.md`](../../planning/INDEX.md) item 2.
