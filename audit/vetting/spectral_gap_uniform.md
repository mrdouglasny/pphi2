# Vetting — `spectral_gap_uniform`

Captured soundness-review records for `spectral_gap_uniform`
(`Pphi2/TransferMatrix/SpectralGap.lean:89`). Linked from
[`../../AXIOM_AUDIT.md`](../../AXIOM_AUDIT.md) and
[`../../planning/INDEX.md`](../../planning/INDEX.md) item 17.

---

```yaml
---
axiom: spectral_gap_uniform
file: Pphi2/TransferMatrix/SpectralGap.lean:89
statement_hash: null
model: gemini (Group 3 external review)
tool: mcp__gemini__deep_think_gemini
source_code: DT, LP
date: 2026-02-23
questions: [typing, strength, non-vacuity, satisfiability]
verdict: SATISFIABLE
rating: Likely correct
discharged: false
superseded_by: null
---
```

**Statement form** (informal): `∃ m₀ > 0, ∃ a₀ > 0, ∀ a ≤ a₀, massGap ≥ m₀` —
the uniform mass gap of the lattice transfer matrix survives the
continuum limit `a → 0`.

**Vetting source.** [`docs/gemini_review.md`](../../docs/gemini_review.md) §"Group 3:
Transfer Matrix and Spectral Gap" / `spectral_gap_uniform` entry.

**Verdict (verbatim):**

> CORRECT — this is the central result of Glimm-Jaffe. Statement form:
> `∃ m₀ > 0, ∃ a₀ > 0, ∀ a ≤ a₀, massGap ≥ m₀`. This correctly captures
> the uniform mass gap bound needed for the continuum limit.
>
> Proof difficulty: VERY HARD — requires Glimm-Jaffe-Spencer cluster
> expansion techniques.
>
> References: Glimm-Jaffe-Spencer (1974), Glimm-Jaffe *Quantum Physics* §19.3.

**Conditions / follow-ups:**

- **Regime-restriction caveat** (from [`planning/INDEX.md`](../../planning/INDEX.md) item 17 +
  [`planning/cyl-2a-spectral-gap.md`](../../planning/cyl-2a-spectral-gap.md)): the axiom
  as stated is **too strong** — φ⁴₂ has a phase transition where the gap closes,
  so the axiom needs a weak-coupling / single-phase hypothesis. The "uniform
  in `a`" is correct; the missing scoping is the coupling regime.
- **Re-vet if strengthened**: any change to the quantifier structure (e.g.
  removing the `∃ a₀` cutoff) requires a fresh deep-think + literature pass.
- **Discharge route**: `a → 0` eigenvalue-gap limit / perturbative analysis
  at weak coupling. The finite-`a` gap `asymGappedTransfer'` is PROVED;
  continuum uniformity remains.

**Cross-references:**

- Discharge plan: [`../../planning/cyl-2a-spectral-gap.md`](../../planning/cyl-2a-spectral-gap.md).
- Status: [`../../planning/INDEX.md`](../../planning/INDEX.md) item 17.
- Downstream consumers: items 14 (`two_point_clustering_from_spectral_gap`),
  15 (`general_clustering_from_spectral_gap`) — ride on the proved B2 trace
  bridge once the gap lands.
