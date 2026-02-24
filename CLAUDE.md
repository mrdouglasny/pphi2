# CLAUDE.md

## Project Overview

Formal construction of the P(Phi)_2 Euclidean quantum field theory in Lean 4,
following the Glimm-Jaffe/Nelson lattice approach. The main theorem constructs
a probability measure on S'(R^2) satisfying all five Osterwalder-Schrader axioms
(OS0-OS4), which by reconstruction yields a Wightman QFT in 1+1d Minkowski
spacetime with a positive mass gap.

See README.md for the full mathematical description and proof outline.

## Build

```bash
lake build
```

The project depends on [gaussian-field](https://github.com/mrdouglasny/gaussian-field)
(expected at `../gaussian-field`) and Mathlib (fetched automatically by lake).

## Status Tracking

After finishing a work sequence (proving axioms, eliminating sorries, or any
code changes), always:

1. Run `./scripts/count_axioms.sh` to get current axiom/sorry counts
2. Update the counts in **status.md** (header line and per-file table)
3. Update the counts in **README.md** (the "Current status" section)
4. Commit status/README updates together with the code changes

## File Structure

```
Pphi2/
  Polynomial.lean               -- Interaction polynomial P(tau)
  WickOrdering/                 -- Phase 1: Wick monomials and counterterms
  InteractingMeasure/           -- Phase 1: Lattice action and measure
  TransferMatrix/               -- Phase 2-3: Transfer matrix, positivity, spectral gap
  OSProofs/                     -- Phase 2-5: Individual OS axiom proofs
    OS3_RP_Lattice.lean         -- Reflection positivity on the lattice
    OS3_RP_Inheritance.lean     -- RP closed under weak limits
    OS4_MassGap.lean            -- Clustering from spectral gap
    OS4_Ergodicity.lean         -- Ergodicity from mass gap
    OS2_WardIdentity.lean       -- Ward identity for rotation invariance
  ContinuumLimit/               -- Phase 4: Embedding, tightness, convergence
  OSAxioms.lean                 -- Phase 6: OS axiom definitions (E2 action, etc.)
  Main.lean                     -- Phase 6: Main theorem assembly
  Bridge.lean                   -- Bridge between pphi2 and Phi4 approaches
scripts/
  count_axioms.sh               -- Axiom/sorry counter
docs/
  axiom_audit.md                -- Self-audit of all axioms
  gemini_review.md              -- External review with references
```

## Lean 4 Working Methods

### Build-First Workflow

Always build before and after changes. Use `lake build` to check the full
project. For faster iteration on a single file, use:
```bash
lake env lean Pphi2/SomeFile.lean
```

### Axiom vs Sorry vs Theorem Conventions

- **`axiom`**: Unproved mathematical statements with real content — things that
  would require a nontrivial mathematical argument to prove. Each axiom should
  have a detailed docstring explaining the mathematical content, proof strategy,
  and references.
- **`sorry`**: Incomplete proofs or definitions where the Lean formalization
  is not yet done, but the mathematical approach is clear.
- **Placeholder `True` conclusions**: Should be `theorem ... := trivial`,
  NOT axioms. Axioms should only be used for substantive mathematical claims.
- When converting an axiom to a theorem, update the inventory tables in
  status.md.
- When introducing new axioms, use `deep_think_gemini` to verify the
  mathematical correctness of each axiom statement before committing.
  Mark unverified axioms with **(NOT VERIFIED)** in status.md.
  Record verification provenance in `docs/axiom_audit.md`.

### Helper Lemma Principle

Only introduce helper lemmas that are **simpler** or **more general** than
the lemma you're using them to prove.

**Good helpers:**
- Atomic mathematical facts (`|e^{it}| = 1`, `cos` bounded by 1)
- Definitional bridges connecting notation to implementation
- Reusable techniques used across multiple proofs
- Standard algebraic identities

**Avoid:**
- Technical infrastructure of similar complexity to the main goal
- Single-use chains that just shuffle hypotheses
- "Setup" lemmas that don't reduce conceptual complexity

### When Stuck on a Proof

Try to **formulate a textbook axiom** — a provable mathematical fact that:
- Uses only Mathlib definitions (no project-specific types)
- Would close the sorry if available
- Is a standard result from Glimm-Jaffe, Simon, Reed-Simon, etc.

This separates the **mathematical content** (the textbook fact) from the
**formalization plumbing** (connecting it to project types). The textbook
fact can often be stated cleanly and its proof attempted independently.

### Common Lean 4 Patterns in This Project

- **Coercion mismatches** between `LinearIsometryEquiv`, `ContinuousLinearEquiv`,
  and plain functions: use `convert` tactic to bridge
- **`ae_of_all μ`** (not `Eventually.of_forall`) for "for all" in ae context
- **`Real.norm_eq_abs`** to bridge `‖x‖` and `|x|` for real numbers
- **`SchwartzMap.compCLMOfAntilipschitz`** for composing Schwartz functions with
  antilipschitz temperate-growth maps
- **`HasTemperateGrowth`** has `.sub`, `.const`, `.comp` combinators

### Before Reverting or Dropping Code

Do not delete significant code without identifying a clear blocker. If blocked:
1. Explain the blocker before deleting
2. Document what was learned (useful Mathlib lemmas, proof strategies, dead ends)
3. Extract value: helper lemmas, mathematical insights, API discoveries

## Skills and Tools

### `/lean-preflight`

Pre-development check: verifies Lean LSP connectivity, git status, toolchain
versions, build status, and axiom/sorry counts. Run at the start of a session
to confirm everything is ready. Defined in `.claude/commands/lean-preflight.md`.

### `/lean4-theorem-proving`

Built-in Claude Code skill for Lean 4 development. Use for:
- Proof development and tactic selection
- Type class synthesis debugging (haveI/letI patterns)
- Mathlib API search and navigation
- Managing sorries and axioms
- Build error diagnosis

### Lean 4 Subagents

Available specialized agents (from lean4-subagents plugin):
- **lean4-sorry-filler** — Fill individual sorries with proofs
- **lean4-sorry-filler-deep** — Deep analysis for harder sorries
- **lean4-proof-repair** — Fix broken proofs after refactoring
- **lean4-axiom-eliminator** — Convert axioms to proved theorems
- **lean4-proof-golfer** — Simplify and shorten existing proofs

### Lean 4 References

Located at `~/.claude/skills/lean4-theorem-proving/references/`:
- `lean-phrasebook.md` — Common Lean 4 patterns and idioms
- `lean-lsp-tools-api.md` — LSP tools for code analysis
- `lean-lsp-server.md` — Server interaction patterns

### Gemini MCP

Available via `chat_gemini` and `deep_think_gemini` MCP tools. Use for:
- Complex mathematical derivations and cross-checking
- Plan review and critique
- Literature and technique suggestions

## Key Mathematical References

- Glimm-Jaffe, *Quantum Physics: A Functional Integral Point of View* (1987)
- Simon, *The P(phi)_2 Euclidean (Quantum) Field Theory* (1974)
- Nelson, "Construction of quantum fields from Markoff fields" (1973)
- Osterwalder-Schrader, "Axioms for Euclidean Green's functions I, II" (1973, 1975)

## Dependencies

- [gaussian-field](https://github.com/mrdouglasny/gaussian-field) at `../gaussian-field` —
  Gaussian free field on nuclear spaces, lattice field theory, FKG inequality
- [Mathlib](https://github.com/leanprover-community/mathlib4) — Lean 4
  mathematics library (fetched automatically)
