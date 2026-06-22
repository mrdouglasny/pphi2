# Vetting — `asymInteractingVariance_le_freeVariance_Lt_uniform`

Captured soundness-review records for
`asymInteractingVariance_le_freeVariance_Lt_uniform`
(`Pphi2/AsymTorus/AsymExpMomentDischarge.lean:206`). Linked from
[`../../AXIOM_AUDIT.md`](../../AXIOM_AUDIT.md) and
[`../../planning/INDEX.md`](../../planning/INDEX.md) item 3.

---

```yaml
---
axiom: asymInteractingVariance_le_freeVariance_Lt_uniform
file: Pphi2/AsymTorus/AsymExpMomentDischarge.lean:206
statement_hash: null
model: gemini-3-pro + codex (multi-pass)
tool: mcp__gemini__deep_think_gemini + codex review
source_code: DT, CX, LP
date: 2026-06-02 (initial) / 2026-06-04 (route correction)
questions: [route-correctness, mode-by-mode-domination, scaling, norm-mismatch]
verdict: SATISFIABLE (corrected form)
rating: Needs review (route under active design)
discharged: false
superseded_by: null
---
```

**Statement form** (informal): the interacting two-point variance is bounded
by the free variance times a constant **uniform in the temporal period `Lt`**
(at fixed spatial extent `Ls`).

**Layer B2** of the Layer-C assembly for
`asymInteracting_expMoment_volume_uniform` (item 1).

**Vetting history:**

This axiom went through two rounds of vetting and a substantial route
correction. Captured in [`docs/B4B5-design.md`](../../docs/B4B5-design.md)
and [`docs/layer-B2-discharge-plan.md`](../../docs/layer-B2-discharge-plan.md):

### Round 1 (2026-06-02, codex + gemini)

Initial "3-piece" form — Källén–Lehmann interacting representation +
mode-by-mode free-covariance domination + cyclic-Young inequality —
was vetted and found **FLAWED but salvageable**:

- (i) The interacting representation must be the periodic **two-arc trace**
  `⟨A Tᵗ A T^{Lt−t}⟩/⟨T^{Lt}⟩` (corollary factor `γ^r + γ^{Nt−r}`), not a
  single-`dist` kernel equality;
- (ii) the scalar free lower bound `Var_free ≳ 1/(1−γ_free)·Σ‖Q‖²` is
  likely **FALSE** for high temporal modes — replace with **mode-by-mode
  free-covariance domination**;
- (iii) `susceptibility_le` is single-vector; a **cyclic Young** lemma is
  needed for the double sum;
- (iv) **Z₂ zero-mean** lemma (raw vs connected 2nd moment);
- (v) reconcile the GJ `a`-weight to avoid double-counting;
- (vi) fixed-`Ls` gap-convergence `m_a → m(Ls) > 0` needed as explicit input.

### Round 2 (Gemini 3.1-pro, 2026-06-02): mode-by-mode is also flawed

The "mode-by-mode" fix is **FALSE** — bare mass `m₀² → −∞` under Wick
ordering; Brascamp–Lieb loses log-concavity. The corrected plan compares
to `Var_free` (an `H⁻¹` space-*time* Sobolev norm); the transfer-matrix
route yields only a *time* gap × *spatial `L²`* norm, and `L² ⊄ H⁻¹`
(NORM MISMATCH; no spatial control).

### Route pivot (2026-06-04, Gemini gemini-3-pro)

**Current live plan: B1 ⊕ gap (resolvent comparison)** —
[`docs/layer-B2-discharge-plan.md`](../../docs/layer-B2-discharge-plan.md)
upgrades pphi2's existing B1 bound `Var_int ≤ C(Lt)·Var_free` (per-`Lt`,
Nelson/chessboard) to `Lt`-uniform via the **proved** operator-norm gap.
The single-slice-stability content is the remaining piece, addressable
via the existing Nelson-estimate infrastructure applied to a single
slice rather than the full volume.

**Concurrent design pin:** [`docs/B4B5-design.md`](../../docs/B4B5-design.md)
(Källén–Lehmann + `1/a` cancellation, Gemini gemini-3-pro 2026-06-04).
Both rest on the same proved gap and may need reconciling into one path.

### Round 3 (Gemini 3.1-pro, 2026-06-22): Route A pinned

Route A — **bounded-cutoff approximation** — is overwhelmingly correct.
Eliminates three alternative routes:
- B (kernel rank-1 split) fails: `⟨g, ·⟩ ∉ L²(ν)` makes the R-term bound
  `∞ · γ^t · ∞` undefined.
- C (eigenbasis via the proved Jentzsch HilbertBasis) needs Mercer's
  theorem (not in Mathlib, massive to formalize).
- D (path-measure direct) would need Brascamp-Lieb on the path measure,
  wasting the proved transfer-operator gap.

Blueprint: truncate `A(ψ) = ⟨g, ψ⟩` to `A_K = clamp(-K, K, ⟨g, ψ⟩)`
(bounded, so `M_{A_K}` is a CLM and `connected_two_point_le` applies),
then take `K → ∞` via DCT. The **a-cancellation trick** decouples `K`
from `a` by bounding the truncated norm by the *exact untruncated*
vacuum variance before any limit. See
[`../../planning/layer-B2-scoping.md`](../../planning/layer-B2-scoping.md).

**Verdict (current):** axiom content sound; proof route pinned as
Route A; **Piece 1 of 5 landed** 2026-06-22
(`Pphi2/AsymTorus/AsymObsTrunc.lean`, 236 lines, 0 sorries, 0 new axioms)
with the truncated-observable multiplication CLM and the a-cancellation
lemma `norm_sq_proj_obsTrunc_omega_le`.

**Conditions / follow-ups:**

- **Operator side built and sorry-free on `main`** (cylinder transfer
  matrix `AsymL2Operator.lean`, `AsymJentzsch.lean`, `AsymPositivity.lean`;
  spectral gap `AsymSpectralGap.lean`; gapped transfer `AsymGappedTransfer.lean`).
  See [`../../AXIOM_AUDIT.md`](../../AXIOM_AUDIT.md) 2026-06-02 entry.
- **Remaining gap**: wire B3→B4→B5 — trace dictionary on the path-measure
  second moment, HS trace-class, B5b single-slice stability + the `1/a`
  cancellation. Active plan: [`docs/B4B5-design.md`](../../docs/B4B5-design.md).
- **Re-vet if strengthened**: the current axiom is the salvageable
  weaker form. Any change to the comparison constant or the variance
  functional requires fresh deep-think.

**Cross-references:**

- Live plans: [`../../docs/B4B5-design.md`](../../docs/B4B5-design.md),
  [`../../docs/layer-B2-discharge-plan.md`](../../docs/layer-B2-discharge-plan.md).
- Superseded: `docs/transfer-instantiation-plan.md` (banner-flagged).
- Status: [`../../planning/INDEX.md`](../../planning/INDEX.md) item 3.
- Downstream: [`asymInteracting_expMoment_volume_uniform.md`](asymInteracting_expMoment_volume_uniform.md) (Layer C).
