# pphi2

Formal construction of the P(Φ)₂ Euclidean quantum field theory in Lean 4,
following the Glimm-Jaffe/Nelson lattice approach.

## What this project proves

**Main theorem** (`Pphi2/Main.lean`): For any even polynomial P of degree ≥ 4
bounded below and any mass m > 0, there exists a probability measure μ on the
space of tempered distributions S'(ℝ²) satisfying all five Osterwalder-Schrader
axioms:

- **OS0 (Analyticity):** The generating functional Z[Σ zᵢJᵢ] is entire analytic
  in z ∈ ℂⁿ.
- **OS1 (Regularity):** ‖Z[f]‖ ≤ exp(c(‖f‖₁ + ‖f‖ₚᵖ)) for some 1 ≤ p ≤ 2.
- **OS2 (Euclidean Invariance):** Z[g·f] = Z[f] for all g ∈ E(2) = ℝ² ⋊ O(2).
- **OS3 (Reflection Positivity):** The RP matrix Σᵢⱼ cᵢcⱼ Re(Z[fᵢ − Θfⱼ]) ≥ 0.
- **OS4 (Clustering):** Z[f + Tₐg] → Z[f]·Z[g] as ‖a‖ → ∞.

By the Osterwalder-Schrader reconstruction theorem, this yields a relativistic
Wightman QFT in 1+1 Minkowski spacetime with a positive mass gap.

This is the theorem originally proved by Glimm-Jaffe (1968–1973), Nelson (1973),
and Simon, with contributions from Guerra-Rosen-Simon and others.

## Proof approach

The construction proceeds in six phases:

1. **Lattice measure** — Define the Wick-ordered interaction
   V_a(φ) = a² Σ_x :P(φ(x)):_a on the finite lattice (ℤ/Nℤ)² and construct
   the interacting measure μ_a = (1/Z_a) exp(−V_a) dμ_{GFF,a}.

2. **Transfer matrix** — Decompose the lattice action into time slices. The
   transfer matrix T is a positive trace-class operator. This gives reflection
   positivity (OS3).

3. **Spectral gap** — Show T has a spectral gap (λ₀ > λ₁) by Perron-Frobenius.
   This gives the mass gap and exponential clustering (OS4).

4. **Continuum limit** — Embed lattice measures into S'(ℝ²), prove tightness
   (Mitoma + Nelson's hypercontractive estimate), extract a convergent
   subsequence by Prokhorov. OS0, OS1, OS3, OS4 transfer to the limit.

5. **Euclidean invariance** — Restore full E(2) symmetry via a Ward identity
   argument. The rotation-breaking operator has scaling dimension 4 > d = 2,
   so the anomaly is RG-irrelevant and vanishes as O(a²) in the continuum limit.
   Super-renormalizability ensures no logarithmic corrections.

6. **Assembly** — Combine all axioms into the main theorem.

## Current status

All six phases are structurally complete and the full project builds
(`lake build`, 3081 jobs). The proof architecture axiomatizes key
analytic/probabilistic results with detailed proof sketches, proves the logical
structure connecting them, and progressively fills in the axioms with full proofs.

- **pphi2:** 26 axioms, 17 sorries
- **gaussian-field** (upstream dependency): 18 axioms, 4 sorries

See [status.md](status.md) for a complete inventory of all axioms and sorries,
organized by difficulty and priority.

## File structure

```
Pphi2/
  Polynomial.lean                    -- Interaction polynomial P(τ)
  WickOrdering/                      -- Phase 1: Wick monomials and counterterms
  InteractingMeasure/                -- Phase 1: Lattice action and measure
  TransferMatrix/                    -- Phase 2-3: Transfer matrix, positivity, spectral gap
  OSProofs/
    OS3_RP_Lattice.lean              -- Phase 2: Reflection positivity on the lattice
    OS3_RP_Inheritance.lean          -- Phase 2: RP closed under weak limits
    OS4_MassGap.lean                 -- Phase 3: Clustering from spectral gap
    OS4_Ergodicity.lean              -- Phase 3: Ergodicity from mass gap
    OS2_WardIdentity.lean            -- Phase 5: Ward identity for rotation invariance
  ContinuumLimit/                    -- Phase 4: Embedding, tightness, convergence
  OSAxioms.lean                      -- Phase 6: OS axiom definitions (matching OSforGFF)
  Main.lean                          -- Phase 6: Main theorem assembly
```

## Dependencies

- [gaussian-field](https://github.com/mrdouglasny/gaussian-field) — Gaussian
  free field on nuclear spaces, lattice field theory, FKG inequality
- [Mathlib](https://github.com/leanprover-community/mathlib4) — Lean 4
  mathematics library

## Building

Requires Lean 4. gaussian-field is a git dependency (fetched automatically).

```bash
git clone https://github.com/mrdouglasny/pphi2.git
cd pphi2
lake build
```

## Documentation

- [status.md](status.md) — Complete axiom/sorry inventory with difficulty
  ratings and priority ordering
- [plan.md](plan.md) — Development roadmap and construction outline
- [docs/axiom_audit.md](docs/axiom_audit.md) — Self-audit of all axioms
  (pphi2 + gaussian-field) with correctness ratings
- [docs/gemini_review.md](docs/gemini_review.md) — External review of axioms
  with references and proof strategies
- [docs/os_axioms_lattice_plan.md](docs/os_axioms_lattice_plan.md) — Design
  notes for OS axiom formulations

## References

- J. Glimm and A. Jaffe, *Quantum Physics: A Functional Integral Point of View*,
  Springer (1987)
- B. Simon, *The P(φ)₂ Euclidean (Quantum) Field Theory*, Princeton (1974)
- E. Nelson, "Construction of quantum fields from Markoff fields," *J. Funct. Anal.* (1973)
- K. Osterwalder and R. Schrader, "Axioms for Euclidean Green's functions I, II,"
  *Comm. Math. Phys.* 31 (1973), 42 (1975)

## Related work

- Xi Yin, [Phi4](https://github.com/xiyin137/Phi4) — Formalization of φ⁴ quantum
  field theory in Lean 4

## License

Copyright (c) 2026 Michael R. Douglas. Released under the Apache 2.0 license.
