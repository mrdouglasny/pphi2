# Vetting — `gaussian_rp_cov_perfect_square`

`Pphi2/OSProofs/OS3_RP_Lattice.lean:648` (**private** scaffolding axiom).

```yaml
---
axiom: gaussian_rp_cov_perfect_square
file: Pphi2/OSProofs/OS3_RP_Lattice.lean:648
visibility: private
statement_hash: null
model: self-audit (scaffolding)
tool: n/a
source_code: SA, LP
date: 2026-02-23
questions: [perfect-square-decomposition]
verdict: SATISFIABLE
rating: Standard
discharged: false
superseded_by: null
---
```

**Statement form** (informal): covariance perfect-square decomposition step
inside the lattice reflection-positivity proof; private scaffolding consumed
only inside `OS3_RP_Lattice.lean`.

**Vetting source.** Reflection-positivity literature
(Osterwalder–Seiler 1978, Glimm–Jaffe §10; pphi2 lattice-RP development).
The general "covariance is a perfect square ⟹ RP" pattern is standard.

**Verdict:** Standard step. Discharge route: explicit `M = A^T A`
factorization of the lattice covariance restricted to the positive-time
half-space.

**Conditions / follow-ups:**

- Not architectural; not enumerated in `planning/INDEX.md`'s 17.
- Could be discharged together with the cylinder-RP development on the
  `reflection-positivity` upstream repo.

**Cross-references:**

- Upstream: [`reflection-positivity`](https://github.com/mrdouglasny/reflection-positivity)
  for the abstract RP machinery.
