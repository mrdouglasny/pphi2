# Vetting — `spectral_gap_lower_bound`

Captured soundness-review records for `spectral_gap_lower_bound`
(`Pphi2/TransferMatrix/SpectralGap.lean:100`). Linked from
[`../../AXIOM_AUDIT.md`](../../AXIOM_AUDIT.md) and
[`../../planning/INDEX.md`](../../planning/INDEX.md) item 16.

---

```yaml
---
axiom: spectral_gap_lower_bound
file: Pphi2/TransferMatrix/SpectralGap.lean:100
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

**Statement form** (informal): `c · mass ≤ massGap` — the lattice mass gap
is bounded below by the bare-mass parameter times a positive constant.

**Vetting source.** [`docs/gemini_review.md`](../../docs/gemini_review.md) §"Group 3" /
`spectral_gap_lower_bound`.

**Verdict (verbatim):**

> CORRECT with caveat. Linear-in-mass bound (gap ≥ c·mass) is correct
> for weak coupling and free field. For strong coupling the relationship
> is more complex, but the existential hides the coupling dependence
> acceptably.
>
> References: "On the Glimm-Jaffe linear lower bound in P(φ)₂" (1972).

**Conditions / follow-ups:**

- **Regime-restricted** (per [`planning/INDEX.md`](../../planning/INDEX.md) item 16):
  FALSE at criticality (`c · mass` linear bound fails when the gap closes).
  Realistic discharge target: weak-coupling `m_phys ≥ m − Cλ` via the existing
  Nelson estimates. The existential `∃ c > 0` form sidesteps the explicit
  coupling but still requires the regime restriction.
- **Discharge route**: cluster expansion / perturbative analysis. Difficulty
  downgrades from ★★★ to ★★ once `spectral_gap_uniform` (item 17) is in
  hand.

**Cross-references:**

- Discharge plan: [`../../planning/cyl-2a-spectral-gap.md`](../../planning/cyl-2a-spectral-gap.md).
- Status: [`../../planning/INDEX.md`](../../planning/INDEX.md) item 16.
