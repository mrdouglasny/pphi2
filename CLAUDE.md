# CLAUDE.md

## Project overview

Formal construction of P(Phi)_2 Euclidean quantum field theory in Lean 4,
following the Glimm-Jaffe/Nelson lattice approach. See README.md for details.

## Build

```bash
lake build
```

## Status tracking

After finishing a work sequence (proving axioms, eliminating sorries, or any
code changes), always:

1. Run `./scripts/count_axioms.sh` to get current axiom/sorry counts
2. Update the counts in **status.md** (header line and per-file table)
3. Update the counts in **README.md** (the "Current status" section)
4. Commit status/README updates together with the code changes

## Key conventions

- `axiom` is used for unproved mathematical statements with real content
- Placeholder statements (conclusion `True`) should be `theorem ... := trivial`,
  not axioms — axioms should only be used for substantive Lean types
- `sorry` marks incomplete proofs or definitions
- When converting an axiom to a theorem, also update the axiom inventory
  tables in status.md

## File structure

```
Pphi2/                          -- Main source
  Polynomial.lean               -- Interaction polynomial P(tau)
  WickOrdering/                 -- Phase 1: Wick monomials and counterterms
  InteractingMeasure/           -- Phase 1: Lattice action and measure
  TransferMatrix/               -- Phase 2-3: Transfer matrix, positivity, spectral gap
  OSProofs/                     -- Phase 2-5: Individual OS axiom proofs
  ContinuumLimit/               -- Phase 4: Embedding, tightness, convergence
  OSAxioms.lean                 -- Phase 6: OS axiom definitions
  Main.lean                     -- Phase 6: Main theorem assembly
  Bridge.lean                   -- Phase 6: Bridge between pphi2 and Phi4 approaches
scripts/
  count_axioms.sh               -- Axiom/sorry counter
```

## Dependencies

- [gaussian-field](https://github.com/mrdouglasny/gaussian-field) at `../gaussian-field`
- Mathlib (fetched automatically by lake)
