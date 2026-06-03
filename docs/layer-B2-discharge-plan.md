# Layer B2 discharge plan — Lt-uniform interacting variance bound

*Refined 2026-06-02 (branch `b2-kallen-lehmann`). Supersedes the chessboard
framing in the `asymInteractingVariance_le_freeVariance_Lt_uniform` docstring.
The transfer-matrix spectral gap this plan rests on is now **proved**.*

## RECONCILED ROUTE (read first): B1 ⊕ gap, not a fresh representation

The authoritative plan is the **B1 ⊕ gap** route already stated in
`Pphi2/AsymTorus/AsymVarianceBound.lean`'s architectural note: B1
(`asymInteractingVariance_le_freeVariance_torus`, **proved** via density-transfer
/ Nelson **hypercontractivity**) gives `Var_int ≤ C(Lt)·Var_free` — `a`-uniform,
norm-correct, but **per-`Lt`**; B2 upgrades `C(Lt)` to a **`Lt`-uniform** constant
using the now-proved transfer-matrix gap (`asymGappedTransfer'` / `susceptibility_le`).

Why this is the right framing (session reasoning + two vettings, 2026-06-02):
- **UV / spatial-Sobolev matching is already done by B1** (Nelson hypercontractivity),
  *not* by a transfer-matrix representation and *not* by Nelson *symmetry* (the 90°
  rotation is a red herring here — it relocates the problem to a swapped-extent
  thermodynamic gap).
- **The gap supplies only the `Lt`/IR uniformity** (clustering; volume-independent,
  unlike B1's extensive Nelson constant).
- The concrete remaining hard step is the **interacting-vs-free resolvent / Toeplitz-form
  comparison** `⟨Q,(1−T̂_int)⁻¹Q⟩ ≤ C·⟨Q,(1−T̂_free)⁻¹Q⟩` that turns B1's `C(Lt)` into
  a `Lt`-uniform `C ≈ m_free/m_int`. (The field-vectors `Q` carry the equal-time
  `H^{−1/2}` covariance, so the naive `L²`-vs-`H⁻¹` mismatch is softened; the danger
  is crudely Young-bounding the time sum and discarding the `p_t` structure.)

**The "interacting Källén–Lehmann *representation* axiom + cyclic-Young" framing in
the sections below was a DETOUR** — both Codex and Gemini-3.1 flagged it (norm
mismatch; false mode-by-mode domination). Keep the sections for the vetting record,
but the live plan is B1 ⊕ gap (resolvent comparison). Older docs
(`asym-interacting-expmoment-volume-uniform-discharge-plan.md`,
`asym-l2-operator-port-scoping.md`) use a yet-earlier split (B1 per-`a`, B2 = UV
chessboard) that is itself superseded now that B1 is `a`-uniform.

## ⚠ Vetting result (Codex, 2026-06-02): the 3-piece sketch below is FLAWED as written

Verdict: **flawed but salvageable**. The idea (gap ⟹ Lt-uniform variance via the
ratio) is sound, but the *as-written* Pieces 1–3 have real gaps. Read the
corrections here first; the sketch in the lower sections is the original, kept
for context. **Required corrections:**

1. **Piece-1 representation is WRONG as an equality.** On the periodic cylinder
   the finite-volume 2-point object is a **two-arc trace**, `⟨A Tᵗ A T^{Lt−t}⟩ / ⟨T^{Lt}⟩`
   (exactly as `reflection-positivity/ReflectionPositivity/VarianceBound.lean`'s
   own docstring states), not `a²·Σ ⟪Q_s, T^{dist(s,t)} Q_t⟫`. The single-`dist`
   kernel is at best a *bound*; the correct periodized factor is `γ^r + γ^{Nt−r}`,
   `r = |s−t| mod Nt`. **Fix:** state Piece 1 as an exact **trace** representation
   with insertion operators `A_s` and the periodic-trace denominator, then derive
   the `γ^r + γ^{Nt−r}` corollary bound.

2. **The free lower bound (Piece 2) is the biggest risk — likely false as stated.**
   `Var_free ≳ (1/(1−γ_free))·Σ_s‖Q_s‖²` uses the *zero-mode* (low-frequency)
   susceptibility scale for **all** test functions; it is not a valid uniform
   lower spectral multiplier for time-dependent profiles with high temporal modes.
   **Fix:** do NOT use a scalar free lower bound. Instead prove **mode-by-mode
   operator domination** — the interacting *connected covariance form* `≤ C ·` the
   *exact free covariance form* — so the comparison is against the true free
   covariance, not a single susceptibility scale. (This also removes the need for
   the `1/a` cancellation to be done "by hand".)

3. **`susceptibility_le` is used beyond its proved scope.** It controls a *single*
   vector (`∑_n |⟪v,Tⁿv⟫| ≤ ‖v‖²/(1−γ)`). The double sum `Σ_{s,t}⟪Q_s,T^d Q_t⟫`
   needs a separate **mixed cyclic Young inequality**:
   `Σ_{s,t<N} γ^{d(s,t)} ‖Q_s‖‖Q_t‖ ≤ (C/(1−γ))·Σ_s‖Q_s‖²` (with the periodic `d`).
   This is a new lemma (candidate for `reflection-positivity`).

4. **Connected vs raw second moment.** The target bounds the *raw* `∫(ωf)²`, but
   the representation/gap argument controls the *connected* (ground-orthogonal)
   part. Add a zero-/one-point lemma (Z₂/evenness of the measure) so raw 2nd
   moment = covariance for these observables, or carry the disconnected term.

5. **`a`-normalization double-counting.** `asymLatticeTestFnIso` already inserts a
   GJ `a` weight (`evalAsymTorusAtSiteGJ_apply = a·…`, `AsymTorusEmbeddingIso.lean:47,76`).
   Pin whether the spatial `a` lives in `A_s` or in the outer `a²`; do not hide it
   in both.

6. **fixed-`Ls` gap convergence is not yet in Lean.** `asymTransferNormalized_gap`
   is per-lattice-parameter; `AsymPositivity.lean:135` puts `a→0` uniformity out of
   scope. Add `m_a → m(Ls) > 0` (equiv. a uniform lower bound on `−log γ_a / a`
   over `Ns·a = Ls`, finitely many coarse spacings handled separately) as an
   explicit lemma/axiom.

**Net:** replacing the black-box B2 axiom with a *correct* trace-representation
axiom is still a genuine improvement, but the discharge needs (i) the two-arc
trace representation, (ii) mode-by-mode free-covariance domination (not a scalar
lower bound), (iii) the cyclic Young lemma, (iv) the Z₂ zero-mean lemma, and
(v) the explicit fixed-`Ls` gap input. (Codex full review: read-only, 2026-06-02.)

## ⚠⚠ Second vetting (Gemini 3.1-pro, 2026-06-02): the corrected plan is STILL flawed — structural norm mismatch

Even with the Codex corrections above, the transfer-matrix discharge does **not**
close B2. A deeper, structural flaw:

1. **NORM MISMATCH (the killer).** The target bounds `Var_int` by the **free
   covariance** `Var_free = ⟨f, (−Δ_{2D}+m²)⁻¹ f⟩` — an `H⁻¹` space-*time* Sobolev
   norm with spatial-gradient suppression `1/(p_s²+p_t²+m²)`. The transfer-matrix
   route (two-arc trace + cyclic Young) yields the **time** gap `1/(1−γ)` times a
   **spatial `L²`** norm of `f`'s slices. Since `L² ⊄ H⁻¹`, a 1D (time) spectral
   gap cannot produce the spatial-gradient bound needed to match `Var_free`.
   *"Without spatial/spacetime symmetry, a 1D transfer-matrix gap will never bound
   a 2D Sobolev norm."* — the chain dies for lack of spatial control.

   **NUANCE to settle (owner):** this objection assumes `‖Q_s‖²` is a raw spatial
   `L²` norm. If `Q_s` lives in the physical Hilbert space with the
   reflection/`B`-inner product, it may already carry spatial covariance structure
   — which is exactly where the objection does or does not bite. **Pin down the
   `Q_s` inner product before any axiom.**

2. **Codex's Piece-2 fix (mode-by-mode domination) is FALSE.** If
   `interacting connected covariance ≤ C·free covariance` held, you'd be done
   immediately and the **entire transfer-matrix apparatus is redundant**. But it
   is analytically false for Wick-ordered φ⁴₂ as `a→0`: Lebowitz/GRS bounds the
   interacting theory by the free one with the **bare** mass
   `m₀² = m_phys² − cλ·log(1/a) → −∞`, so the bounding covariance diverges;
   Brascamp–Lieb needs log-concavity, destroyed by the `−log(1/a)·φ²` counterterm.
   (Consistent with the earlier literature vetting: Wick ordering breaks the naive
   comparison.)

3. **What stands.** The **two-arc trace + `γʳ+γ^{Nt−r}` + cyclic Young** is correct
   and sufficient for the **`Lt`-direction time-sum only**
   (`‖γʳ+γ^{Nt−r}‖_{L¹(Z_{Nt})} ≤ 2/(1−γ)`). The periodized kernel is mandatory.

4. **Salvage — Nelson symmetry.** To bridge time→space without the (forbidden)
   chessboard, use **Nelson symmetry** (Euclidean rotation invariance of the
   measure): the spatial transfer matrix behaves like the time one, reconstructing
   the `1/(p_s²+p_t²+m²)` free covariance. Standard Glimm–Jaffe/Simon Route C uses
   the **chessboard** (FSS) for exactly this rotation; Nelson symmetry is the
   alternative.

5. **Implication for the architecture.** pphi2's **B1 already achieves the
   norm-match via Nelson** (the `asymNelson` exp-moment / density-transfer route).
   So the discharge most likely must **combine** B1's Nelson-based norm-matching
   (per-`Lt`) with the transfer-matrix gap supplying **`Lt`-uniformity** — NOT
   represent `Var_int` directly as a transfer-matrix sum and compare to `Var_free`.
   The transfer-matrix work (Part A + #1) provides the `Lt`-uniform time-decay; it
   does not, by itself, provide the spatial/Sobolev match.

**RECOMMENDATION: do not write any representation axiom until the norm-mismatch /
`Q_s`-inner-product question is settled.** Two independent vettings (Codex,
Gemini 3.1-pro) now flag the direct transfer-matrix-vs-`Var_free` route as
broken; the viable path is the Nelson-symmetry bridge or a B1⊕(TM-`Lt`-uniformity)
combination. This is an owner-level design decision.

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
