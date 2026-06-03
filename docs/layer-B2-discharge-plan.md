# Layer B2 discharge plan — Lt-uniform interacting variance bound

*Refined 2026-06-02 (branch `b2-kallen-lehmann`). Supersedes the chessboard
framing in the `asymInteractingVariance_le_freeVariance_Lt_uniform` docstring.
The transfer-matrix spectral gap this plan rests on is now **proved**.*

## Target (the axiom to discharge)

`asymInteractingVariance_le_freeVariance_Lt_uniform`
(`Pphi2/AsymTorus/AsymExpMomentDischarge.lean:190`):

> ∃ `C > 0` (depending only on `P, mass, Ls`) such that for **all** `Lt`, `Nt,
> Ns, a` with `Nt·a = Lt`, `Ns·a = Ls`, and all test functions `f`:
> `∫(ω f)² dμ_int ≤ C · ∫(ω g)² dμ_GFF`, `g = asymLatticeTestFnIso … f`.

`C` must be uniform in **both** `Lt → ∞` (IR) **and** `a → 0` (UV), at fixed `Ls`.

## Resolved architecture (no chessboard; fixed `Ls`)

See `reflection-positivity/docs/B2_UNIFORMITY_QUESTION.md` (expert-vetted):

- **No chessboard / FSS needed**, *because `Ls` is fixed.* The fixed-`Ls`
  cylinder mass gap `m_a → m(Ls) > 0` by compact-resolvent + norm-resolvent
  convergence `T_a → e^{−a H(Ls)}` (Simon "P(φ)₂" 1974 Ch. VI; Thm V.15).
  FSS/chessboard is only for the thermodynamic `Ls → ∞` limit.
- **The `1/a`-cancellation trap is decisive.** `susceptibility_le` gives
  `Σ_{t<Nt} γ^t ≤ 1/(1−γ)` with `γ = e^{−m_a a}`, so `1/(1−γ) ≈ 1/(m_a a)`
  **diverges as `1/a`**. A single axiom `Var_int ≤ 1/(1−γ)·Var_free` is therefore
  `a`-NON-uniform and WRONG. The `1/a` must cancel inside the **ratio** of the
  interacting and free transfer-matrix representations (both carry the same `a²`
  spacetime measure and the same `1/a` geometric-sum factor), leaving
  `C ≈ m_free/m_int`, finite and `a`-uniform.

## Already proved (do not re-derive)

- `reflection-positivity` (v4.30.0, dep of pphi2): `GappedTransfer` and
  `GappedTransfer.susceptibility_le`:
  `∑_{n<N} |⟪v, Tⁿ v⟫| ≤ ‖v‖²/(1−γ)`, **uniform in `N`** (the `Lt` direction).
- `Pphi2/AsymTorus/AsymGappedTransfer.lean`: `asymGappedTransfer` packaging.
- `Pphi2/AsymTorus/AsymSpectralGap.lean`: `asymTransferNormalized_gap` (the
  operator-norm gap on the ground-orthogonal complement) and `asymGappedTransfer'`
  (the `GappedTransfer` with no hypotheses). So `susceptibility_le` applies to the
  asym cylinder off the shelf.
- `AsymJentzsch`/`AsymPositivity`: `AsymTransferGroundExcitedData.htop` (the
  Perron-Frobenius dominance pinning the ground index as the spectral top).

## The three remaining pieces

### Piece 1 — interacting Källén–Lehmann representation (the new axiom)

The genuinely un-formalized Feynman–Kac fact (TransferMatrix.lean's docstring:
*"the trace formula … is a standard identity but not formalized here"*). State,
for the cylinder interacting measure, the time-slice decomposition of the
2-point function as a normalized transfer-matrix Toeplitz form:

```
∫(ω f)² dμ_int  =  a² · Σ_{s,t < Nt} ⟪Q_s(f), (asymTransferNormalized)^{dist(s,t)} (Q_t(f))⟫
```

where `Q_s(f) : L2SpatialField Ns` is the spatial field-vector of `f` at time
slice `s` projected onto the ground-orthogonal complement (connected part),
and `dist(s,t)` is the periodic-time distance on `Z_{Nt}`. (Precise statement:
isolate `Q` and the connected/disconnected split carefully; verify
non-vacuity and correct quantifiers per the axiom protocol; mark NOT VERIFIED
and **vet with deep-think + Codex before relying** — the axiom statement is the
delicate part.)

References: Glimm–Jaffe "Quantum Physics" Ch. 6 (lattice transfer matrix);
Simon "P(φ)₂" (1974) Ch. III; Osterwalder–Schrader. This axiom is **more
fundamental** than B2 — it is the representation; all operator-theoretic content
(gap, geometric series) is now proved.

### Piece 2 — free Källén–Lehmann representation (provable, not an axiom)

The free side is Gaussian and explicitly computable. pphi2 already has
`∫(ω g)² dμ_GFF = ⟪T g, T g⟫` (`AsymContinuumLimit.lean:163`,
`second_moment_eq_covariance`). Derive the matching free transfer-matrix
Toeplitz form `a² · Σ_{s,t} ⟪Q_s, T_free^{dist(s,t)} Q_t⟫` and the **lower bound**
`Var_free ≳ (1/(1−γ_free))·‖Q‖²`-scale, so the `1/a` factors match the
interacting side. (Free, so no axiom needed — this is the key to the ratio.)

### Piece 3 — the ratio (proved; the `1/a` cancellation)

Combine: interacting upper bound (Piece 1 + `susceptibility_le`, giving the
`1/(1−γ_int)` factor) over free lower bound (Piece 2, the `1/(1−γ_free)` factor).
The `a²` and the leading `1/a` are common factors that cancel **before** any
`a → 0` limit (keep everything in dimensionless ratio form; never evaluate
`1/(1−γ)` standalone). Result: `C ≈ (1−γ_free)/(1−γ_int) × (overlap) → m_free/m_int`,
finite and uniform in `Lt` and `a`. The `a`-uniformity of `C` reduces to the
fixed-`Ls` gap convergence `m_a → m(Ls) > 0` (compact resolvent — a separate,
non-chessboard input; can be its own lemma/axiom).

## Net

- **Axioms**: replace the high-level B2 axiom with **one** more-fundamental
  Feynman–Kac representation axiom (Piece 1). Net axiom-quality improvement:
  the operator-theoretic content (the hard part historically) is now proved.
- **Proofs**: Pieces 2 (free representation) and 3 (ratio) are provable from
  existing infrastructure + the proved `susceptibility_le`.
- **Sequencing**: state + vet the Piece-1 axiom; prove Piece 2; prove Piece 3;
  prove `fixed-Ls gap convergence` (or take as a small, clearly-cited lemma);
  assemble into the discharge theorem; remove the B2 axiom.
