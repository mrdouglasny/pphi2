# Layer B2 — wiring scope + PR plan

**Current target axiom.**
`asymInteractingVariance_le_freeVariance_lattice_Lt_uniform`
(`Pphi2/AsymTorus/AsymExpMomentDischarge.lean:215`). The former torus
declaration `asymInteractingVariance_le_freeVariance_Lt_uniform` is now a
theorem assembled from this lattice input plus the torus→lattice pushforward.

```lean
axiom asymInteractingVariance_le_freeVariance_lattice_Lt_uniform
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Ls : ℝ) [Fact (0 < Ls)] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Lt : ℝ) [Fact (0 < Lt)] (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
        (a : ℝ) (ha : 0 < a),
        (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls →
        ∀ (G : AsymLatticeField Nt Ns),
          ∫ ω, (ω G) ^ 2
            ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) ≤
          C * ∫ ω, (ω G) ^ 2
              ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)
```

The same shape as B1 (proved) but with `C` chosen **before** the `Lt`
quantifier — `Lt`-uniform. B1 supplies a per-`Lt` `C(Lt)` via
Nelson/Gaussian-domination; B2 lifts it to `Lt`-independent via the
transfer-matrix gap + a geometric series.

**Live design**: this file (Route A, gemini-vetted 2026-06-22, Round 3).
The earlier kernel-side / HS-Cauchy-Schwarz design in
[`../docs/B4B5-design.md`](../docs/B4B5-design.md) (2026-06-04) is
**superseded** as the route plan; it remains useful as background on
the proved infrastructure and the route-correction history.

**Route correction noted**: the original "HS kernel Cauchy-Schwarz"
six-brick plan was **abandoned 2026-06-04** (recorded in
`Pphi2/AsymTorus/AsymTraceBridge.lean:18-46`): op-norm ≤ HS-norm is the
wrong direction, so HS bricks 3-6 cannot feed off the operator gap
alone. The live path is the **GNS/operator route** below.

## Infrastructure already on `main` (all sorry-free)

### Operator-level decay bricks — PROVED in `Pphi2/AsymTorus/AsymTraceBridge.lean`

| Brick | Theorem | What |
|---|---|---|
| **Ω as eigenvector** | `asymTransferOperatorCLM_groundVector` | `T Ω = λ₀ • Ω` |
| **Ω-power identity** | `asymTransferOperatorCLM_pow_groundVector` | `T^m Ω = λ₀^m • Ω` |
| **Normalized form** | `asymTransferOperatorCLM_eq_smul_normalized` | `T = λ₀ • T̂` |
| **Perp decay** | `asymTransferOperatorCLM_pow_norm_le_of_perp` | `‖T^{m+1} v‖ ≤ (γλ₀)^{m+1} ‖v‖` for `v ⊥ Ω` |
| **Ω-normalization** | `asymGroundVector_norm_eq_one` | `‖Ω‖ = 1` |
| **Sub-groundProj contraction** | `norm_sub_groundProj_le` | `‖v − ⟪Ω,v⟫·Ω‖ ≤ ‖v‖` |
| **Rank-1 operator decay** | `asymTransferOperatorCLM_pow_sub_groundProj_norm_le` | `‖T^{m+1} v − λ₀^{m+1}·⟪Ω,v⟫·Ω‖ ≤ (γλ₀)^{m+1}·‖v‖` |

These ARE "Bricks 0-2" in operator form. Nothing more needed at this
layer.

### Other inputs

| Where | Theorem(s) |
|---|---|
| `Pphi2/AsymTorus/AsymTransferKernelOperator.lean` | `asymTransferOperatorCLM_apply` (operator↔kernel for `T`); `asymTransferKernel_kPow_apply` (operator↔kernel for `T^{m+1}`) |
| `Pphi2/AsymTorus/AsymVarianceDischarge.lean` | `interacting_second_moment_eq_pathMeasure` (B3 — torus 2nd moment as path-measure 2nd moment); `asym_pairing_sum_slice`, `config_pairing_eq_slice` (slice decomposition) |
| `Pphi2/AsymTorus/AsymVarianceBound.lean` | `asymInteractingVariance_le_freeVariance_lattice` / `_torus` (**B1**, per-`Lt` `C(Lt)` from Nelson) |
| `Pphi2/AsymTorus/AsymGappedTransfer.lean` | `asymGappedTransfer'` (hypothesis-free `GappedTransfer` packaging); `asymTransferNormalized_gap`, `asymTransferGroundEigenvalue_pos` |
| `../reflection-positivity/.../TransferSystem.lean` | `twoPoint_dictionary` (path-measure two-point = kernel-integral form) |
| `../reflection-positivity/.../ConnectedTwoPoint.lean` | `vacuumPerp`, `two_point_split`, **`connected_two_point_le`** (operator form: `|⟪Ω,M_A T^d M_B Ω⟫ − ⟪Ω,M_A Ω⟫·⟪Ω,M_B Ω⟫| ≤ γ^d · ‖P₁(M_A Ω)‖·‖P₁(M_B Ω)‖`), **`connected_susceptibility_le`** |
| `../reflection-positivity/.../AveragedSusceptibility.lean` | `geom_wrap_sum_le`, `averaged_susceptibility_bound` |

## Route verdict (gemini deep-think 2026-06-22, 2m23s)

**Route A — bounded-cutoff approximation** is overwhelmingly correct.

The technical hurdle (slice-pairing observable `A(ψ) = ⟨g_t, ψ⟩` is
unbounded, so `M_A` isn't a CLM and `connected_two_point_le` doesn't
literally apply) is resolved by truncating each observable to bounded
`A_{K,t}(ψ) := clamp(-K, K, ⟨g_t, ψ⟩)`, applying the operator-form
bounds at finite `K`, then taking `K → ∞` via dominated convergence
on the path measure (dominator integrable by B1).

Routes eliminated:
- **B (rank-1 kernel split)**: fails because `⟨g, ·⟩ ∉ L²(ν)` makes the
  `R`-term bound `∞ · γ^t · ∞` undefined.
- **C (eigenbasis via Jentzsch HilbertBasis)**: needs Mercer's theorem
  (∫k(x,x)dν = Σ λ_i, integrand-not-just-trace) which isn't in Mathlib
  and is massive to formalize.
- **D (path-measure direct)**: would need Brascamp-Lieb-style decay on
  the path measure, completely wasting the proved transfer-operator gap.

### The `a`-cancellation trick (resolves the crux-2-style concern)

The lattice test function carries an `a`-factor
(`asymLatticeTestFnIso = a · evalAtSite`), so `g_t = a · δ_{site}`. A
nonlinear `clamp` could break the `a`-cancellation between
`int/free`. The fix: bound the truncated norm by the **untruncated**
norm *before* summing.

```
‖P₁(M_{A_{K,t}} Ω)‖²_{L²}              ≤ ‖M_{A_{K,t}} Ω‖²_{L²}
                                      = ∫ A_{K,t}(x)² · Ω(x)² dν
since |A_{K,t}(x)| ≤ |⟨g_t, x⟩|:       ≤ ∫ ⟨g_t, x⟩² · Ω(x)² dν
                                      = ‖M_{⟨g_t, ·⟩} Ω‖²_{L²}    (RHS exact)
```

The RHS is the **exact** vacuum variance of the *un*truncated linear
observable. The `a` from `g_t = a·δ_{site}` pulls out as `a²`
unconditionally; `K` is fully decoupled from `a`. The
crux-2-style error mode is avoided by construction.

## Remaining work — corrected route (Route A blueprint)

Five pieces, not six bricks. The operator-route bypasses HS entirely.

### Piece 1 — Truncated-observable + a-cancellation lemma *(first PR target)*

The atomic Route-A building block, isolated from the dictionary
plumbing. New file `Pphi2/AsymTorus/AsymObsTrunc.lean`. Targets:

```lean
/-- Truncated slice observable. Bounded by `K`, hence `L^∞`. -/
def asymSliceObsTrunc (g : SpatialField Ns) (K : ℝ) : SpatialField Ns → ℝ :=
  fun ψ => max (-K) (min K (∑ i, g i * ψ i))

/-- The a-cancellation lemma: bound the truncated projection norm by the
exact untruncated vacuum variance. `K` decouples from any other parameters
(including the lattice spacing `a` carried by `g`). -/
theorem norm_sq_proj_obsTrunc_omega_le
    (g : SpatialField Ns) (K : ℝ) (hK : 0 ≤ K) (Ω : SpatialField Ns → ℝ)
    (hΩ : Integrable (fun x => (∑ i, g i * x i)^2 * Ω x ^ 2) volume) :
    ‖M_{A_K} Ω - ⟪Ω, M_{A_K} Ω⟫ • Ω‖²_{L²(volume)}
      ≤ ∫ x, (∑ i, g i * x i)^2 * Ω x ^ 2 ∂volume
```

Proof: chain
`‖P₁(M_{A_K} Ω)‖² ≤ ‖M_{A_K} Ω‖² ≤ ∫ A_K² Ω² ≤ ∫ ⟨g,·⟩² Ω²` —
last step uses `|A_K(x)| ≤ |⟨g, x⟩|` pointwise.

**Sub-lemmas needed (small):**

* `asymSliceObsTrunc_abs_le_linear` — `|A_K(ψ)| ≤ |⟨g, ψ⟩|` pointwise.
* `asymSliceObsTrunc_bounded` — `|A_K(ψ)| ≤ K`.
* `asymSliceObsTrunc_measurable` — measurability.

**Estimated**: ~100-200 lines. Self-contained — uses existing `mulCLM`
(in `L2Multiplication.lean`) and Mathlib's `norm_sub_inner_*` /
`vacuumPerp`-style API. No new axioms.

### Piece 2 — Apply `averaged_susceptibility_bound` at finite K

With Piece 1's bound on `‖P₁(M_{A_K} Ω)‖` and the proved
`asymTransferOperatorCLM_pow_sub_groundProj_norm_le`, instantiate
`connected_two_point_le` for the bounded operators `M_{A_{K,t}}` and
sum via `averaged_susceptibility_bound`. AM-GM `2xy ≤ x² + y²`
decouples `(t, t')`. Result: a `K`-uniform `Lt`-uniform bound

```
∫ (∑_t A_{K,t}(ψ_t))² dpathMeasure
  ≤ (2C/(1-γ)) · Σ_t ∫ x, ⟨g_t, x⟩² · Ω(x)² dν
```

The RHS is `K`-independent (Piece 1's bound removed it). Dictionary
bridge (path-measure ↔ kernel form) goes here via `twoPoint_dictionary`.

**Estimated**: ~200-300 lines.

### Piece 3 — K → ∞ via dominated convergence

Pointwise `A_{K,t}(ψ) → ⟨g_t, ψ⟩` as `K → ∞`. Dominator on the path
measure:
```
G(ω) := (Σ_t |⟨g_t, ω_t⟩|)² ≤ Lt · Σ_t ⟨g_t, ω_t⟩².
```
Each `∫ ⟨g_t, ω_t⟩² dpathMeasure < ∞` by B1 (`asymInteractingVariance_le_freeVariance_lattice`),
so `G ∈ L¹(dpathMeasure)`. DCT then closes:

```
∫ (∑_t ⟨g_t, ω_t⟩)² dpathMeasure  ≤  (2C/(1-γ)) · Σ_t ‖M_{⟨g_t,·⟩} Ω‖²_{L²}
```

This is the path-measure variance bound, `Lt`-uniform.

**Estimated**: ~100-200 lines.

### Piece 4 — B5b single-slice stability

The constant `‖P₁ Φ Ω‖²` in the bound from pieces 2-3 must be bounded
by `C · Var_free,slice(Φ)` with `C` independent of `a, Nt`. Per design
doc `docs/B4B5-design.md` §"Parallel-investigation findings", this is
the **`Ls`-fixed single-time-slice specialization** of the existing
Nelson engine `asymNelson_exponential_estimate_iso` (`AsymNelson.lean`)
— not a new deep theorem.

**Vet first.** The exact `a`-power bookkeeping should be derived +
gemini-vetted before formalizing (same discipline that caught the
crux-2 `a`-power error).

**Estimated**: ~200-400 lines.

### Piece 5 — Final assembly

Compose pieces 1-4 + the torus→lattice pushforward
(`asymTorusInteractingMeasureIso = (μ_int^{lattice}).map ι`,
`ι = asymTorusEmbedLiftIso`) + `interacting_second_moment_eq_pathMeasure`
(B3) → convert `axiom asymInteractingVariance_le_freeVariance_Lt_uniform`
to a `theorem`.

**Estimated**: ~50-100 lines.

## Aggregate estimate

| Phase | Lines | Difficulty |
|---|---|---|
| Piece 1 (dictionary→operator) — **first PR** | 150-300 | ★★ (measure normalization is fiddly) |
| Piece 2 (connected_two_point_le) | 100-200 | ★ (composition) |
| Piece 3 (geom_wrap_sum_le) | 100-200 | ★ (composition) |
| Piece 4 (B5b) | 200-400 | ★★ (vet `a`-powers first) |
| Piece 5 (final assembly) | 50-100 | ★ (wiring) |
| **Total** | **600-1200** | ★★ |

**Wall-clock**: ~1.5-3 active weeks (smaller than the original 6-brick
estimate because the operator-route bypasses HS bookkeeping entirely).
Discharges 1 architectural axiom directly; unlocks items 14 + 15
(`two_point_clustering_from_spectral_gap`,
`general_clustering_from_spectral_gap`) via the B2 trace dictionary,
making them ★★ instead of blocked on the square trace dictionary.

## First PR — Piece 1 (truncated observable + a-cancellation lemma)

The atomic Route-A building block. Self-contained — uses only the
already-landed `mulCLM` and basic Mathlib `L²` API.

Target: new file `Pphi2/AsymTorus/AsymObsTrunc.lean`. Key declarations:

* `asymSliceObsTrunc g K : SpatialField Ns → ℝ` — the truncated slice
  observable `clamp(-K, K, ⟨g, ψ⟩)`.
* `asymSliceObsTrunc_abs_le_linear` — `|A_K(ψ)| ≤ |⟨g, ψ⟩|` pointwise.
* `asymSliceObsTrunc_bounded` — `|A_K(ψ)| ≤ K`.
* `asymSliceObsTrunc_measurable` — measurability.
* `asymSliceObsTrunc_mulCLM` — the multiplication-by-`A_K` CLM on
  `L²(volume)` via `mulCLM`.
* **The a-cancellation lemma** `norm_sq_proj_obsTrunc_omega_le`:
  the truncated-projection L²-norm is bounded by the **exact** vacuum
  variance of the *untruncated* linear observable, with no `K`-dependent
  factor. (See gemini verdict above.)

* No new axioms expected.
* `lake build` green; `audit/axiom-report.txt` unchanged.
* Update `planning/INDEX.md` item 3 to mark Piece 1 as done.
* Update `audit/vetting/asymInteractingVariance_le_freeVariance_Lt_uniform.md`
  with progress note + route verdict.

Ready to write.
