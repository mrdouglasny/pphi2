# Vetting — `asymInteractingVariance_le_freeVariance_lattice_Lt_uniform`

```yaml
---
axiom: asymInteractingVariance_le_freeVariance_lattice_Lt_uniform
file: Pphi2/AsymTorus/AsymExpMomentDischarge.lean
statement_hash: null
model: codex implementation audit
tool: local Lean build + Layer-B2 Route-A assembly review
source_code: CX, LP
date: 2026-06-23
questions: [lattice-final-assembly, torus-pushforward, remaining-route-a-gap]
verdict: SATISFIABLE PENDING ROUTE-A COMPLETION
rating: Narrow lattice Route-A final input
discharged: false
superseded_by: null
---
```

**Statement form.** At fixed spatial circumference `Ls`, there is a constant
`C > 0`, uniform in the time period `Lt` and the lattice refinement
`(Nt, Ns, a)`, such that every lattice test field `G : AsymLatticeField Nt Ns`
satisfies

`∫ (ω G)^2 dμ_int^lattice <= C * ∫ (ω G)^2 dμ_free^lattice`.

**Why this replaces the former torus axiom.** The old torus-level axiom
`asymInteractingVariance_le_freeVariance_Lt_uniform` is now a theorem. Its
proof is purely structural: pull the torus interacting measure back along
`asymTorusEmbedLiftIso`, use `asymTorusEmbedLiftIso_eval_eq` to identify the
torus pairing with the lattice pairing against `asymLatticeTestFnIso`, then
apply this lattice input.

**Why this is the smallest active input.** Piece 4 already proves the final
lattice-form handoff
`interacting_second_moment_bound_to_lattice_free_covariance`, but it remains
parameterized by the Route-A finite-K/DCT package and by the free-side assembly
hypothesis `hFreeAssemble`. The latter is intentionally explicit because the
known standalone `1/(1 - gamma)` shortcut is `a`-non-uniform. This axiom is the
closed lattice statement that those remaining hypotheses must eventually prove.

**Discharge plan.** Close the finite-K time-family estimate, package the
`K -> infinity` theorem into the exact Piece-3 `hPiece3` form, discharge B5b
`groundVariance_le_freeCovariance`, and prove the free-side assembly in the same
a-power convention as `latticeCovarianceAsymGJ`. Then replace this axiom with
the assembled theorem and re-run `audit/axiom_report.lean`.
