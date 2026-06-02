# Asym transfer-operator port (Layer B1 scoping)

*2026-05-31. Independent of the lee-yang gemini vet — Layer B1 is
needed regardless of which Layer-A architecture wins.*

## Goal

Discharge **Layer B1** of the
`asymInteracting_expMoment_volume_uniform` discharge plan:

> At fixed `(a, Ns)`, the cylinder transfer matrix has a positive,
> isolated mass gap, and the lattice Källén-Lehmann sum rule gives
> `Var_int(⟨ω, f⟩) ≤ C(a, Ns) · Var_free(⟨ω, f⟩)`.

(Layer B2 = uniformity of `C(a, Ns)` as `a → 0`, `Ns → ∞`. Out of
scope here; shares discharge path with the square's open
`spectral_gap_uniform`.)

## What already exists (square track) — reusable

The square has a fully built transfer-operator infrastructure
(`Pphi2/TransferMatrix/`, ~3500 lines):

| File | Lines | Content | Generic? |
|---|---|---|---|
| `L2Multiplication.lean` | 163 | `mulCLM` (multiplication by bounded function) | ✅ fully generic over `(α, μ)` |
| `L2Convolution.lean` | 621 | `convCLM` (convolution with L¹ kernel), Young's inequality, self-adjointness for even kernels | ✅ fully generic over Haar group |
| `GeneralResults/HilbertSchmidt.lean` | 603 | `integral_operator_l2_kernel_compact` (general L²-kernel → HS → compact) | ✅ fully generic |
| `L2Operator.lean:585` `hilbert_schmidt_isCompact` | ~50 | `M_w ∘ Conv_g ∘ M_w` is compact when `w ∈ L² ∩ L∞`, `g ∈ L¹`, `‖g‖_∞ ≤ 1` | ✅ generic in the operator shape (used by square) |
| `JentzschProof.lean` | 1082 | Full Jentzsch theorem: compact + positivity-improving + self-adjoint ⟹ isolated simple top eigenvalue with positive eigenvector | ✅ generic over abstract Hilbert space |

So: **none of the heavy general machinery needs to be ported.**

## What's missing — the asym instantiation

Square-specific files that need asym analogues:

| Square file | Square line count | Asym port needed | Notes |
|---|---|---|---|
| `L2Operator.lean` (defs + asym-specific lemmas) | 673 (28 decls) | **~300-400 lines** | port `transferWeight`, `transferGaussian`, `transferOperatorCLM`, `_isSelfAdjoint`, `_isCompact`. Sub-lemmas (`_measurable`, `_bound`, `_memLp`, `_memLp_two`, `_pos`, `_norm_le_one`, `_decay`) port mechanically. |
| `Jentzsch.lean` (asym applications of generic Jentzsch) | 515 (9 decls) | **~200-300 lines** | port `transferOperator_positivityImproving`, `_strictly_positive_definite`, `_inner_nonneg`, `_eigenvalues_pos`, `_ground_simple`, `_ground_simple_spectral`. Most reuse `jentzsch_theorem` directly. |
| `Positivity.lean` (energy levels) | 145 (8 decls) | **~100 lines** | `asymGroundEnergyLevel`, `asymFirstExcitedEnergyLevel`, `asymMassGap`, `asymMassGap_pos`. |
| `SpectralGap.lean` (the PROVED part — `spectral_gap_pos` only) | 65 (1 decl, plus the open axiom) | **~30 lines** | `asymSpectral_gap_pos`. Skip the analogue of the open `spectral_gap_uniform` (that's Layer B2). |

**Port subtotal: ~630-830 lines** — mechanical, with one design call (next §).

## The one design call — Wick-constant convention

Subtle point: the square's `transferWeight` uses `wickConstant 1 Ns a mass`
(the `d=1` spatial-only Wick constant). For the cylinder transfer
matrix, the Wick ordering on the time-slice action should be relative
to *some* Wick constant — but which?

* **Option α**: use the square's `wickConstant 1 Ns a mass`. Treats the
  spatial slice as if it were an isolated 1D system; doesn't see the
  asym dispersion.
* **Option β**: use the asym joint `wickConstantAsym Nt Ns a mass`.
  The Wick ordering reflects the full 2D measure the slice sits in.
* **Option γ**: use a new "slice Wick constant" defined to make the
  Wick mean of the slice action vanish under the cylinder Gibbs measure.

The math literature consistently uses option β for cylinder
constructions (the Wick ordering is tied to the joint measure's
covariance, not to the spatial-only marginal). The pphi2 `asymCylinder`
existing infrastructure (e.g. `interactionFunctionalAsym`) uses
`wickConstantAsym` everywhere, so option β is also the consistent
choice from pphi2's own perspective.

**Decision flagged**: the port should define
`asymTransferWeight P a mass := exp(-(a/2) · asymSpatialAction Ns P a mass (wickConstantAsym Nt Ns a mass))`
or a per-slice variant. The exact form needs one careful pass to make
sure `asymTransferOperator_isSelfAdjoint` and `_positivityImproving`
still go through cleanly with the joint Wick constant (they should —
both arguments are about the operator's kernel, which depends on the
weight only through `M_w`).

## What's genuinely new — Källén-Lehmann variance bound

The above ports give: `asymCylinderTransferOperator` is compact,
self-adjoint, positivity-improving ⟹ isolated simple top eigenvalue
λ₀ with positive eigenvector ⟹ mass gap `m_phys = -(1/a) log(λ₁/λ₀) > 0`.

This is the same shape the square produces. **The square does NOT
have**, on either side, the next step:

> `m_phys > 0` ⟹ `Var_int(⟨ω, f⟩) ≤ C(a, Ns) · Var_free(⟨ω, f⟩)` via
> the lattice Källén-Lehmann spectral representation.

The standard derivation (Glimm-Jaffe §6.2, §19.3):

1. Express `⟨(ω f) (ω f)⟩_int = ∫∫ f(x) f(y) S_2(x, y) dx dy` where
   `S_2` is the interacting 2-point function.
2. Spectral resolution: `S_2(x, y) = ∫ exp(-m·|t_x - t_y|) dρ(m)` for
   some positive measure `ρ` supported on `[m_phys, ∞)` (Källén-Lehmann).
3. Bound `dρ` by the corresponding free-field spectral measure (since
   the support is shifted to `[m_phys, ∞)` and the total mass is
   bounded by the operator norm of the transfer matrix).
4. Conclude `Var_int(⟨ω, f⟩) ≤ (sup-over-spectral-weights) · Var_free(⟨ω, f⟩)`.

**Scope estimate**: **~400-800 lines**, with one big risk —

### Risk: Mathlib spectral-theorem state

Step (3) uses the spectral theorem for bounded self-adjoint operators
to extract `dρ`. Lean's spectral theorem is WIP (gemini flagged this
in the vet of the broader discharge architecture). Realistic
workarounds:

* **Bespoke functional calculus** for `T = transferOperatorCLM`: since
  `T` is *explicit* (`M_w ∘ Conv_G ∘ M_w` with explicit Gaussian
  kernel), maybe build `S_2` via direct computation of `T^n` matrix
  elements and bound it by the geometric series `Σ λ₁ⁿ` rather than via
  abstract spectral theory. Avoids Mathlib's WIP spectral theorem.
* **Settle for the bound via Fourier on the asym lattice**: the asym
  lattice is *finite* and circulant per direction, so its eigenbasis is
  explicit (`massEigenvectorBasisAsym`); the spectral representation
  is just a finite sum over modes, no spectral theorem needed.

The Fourier approach is **probably the cleanest**: the asym lattice is
finite-dimensional per `(Nt, Ns, a)`, so all spectral statements are
genuinely finite linear algebra. The Källén-Lehmann shape is then a
direct eigenmode sum with the explicit asym dispersion eigenvalues.
This would also cleanly match the Layer B2 chessboard argument later.

Revised B1-final estimate with Fourier route: **~250-500 lines** for
the Källén-Lehmann step.

## Total Layer B1 scope

| Sub-piece | Lines | Type |
|---|---|---|
| Asym TM compactness + self-adjointness port | ~300-400 | Mechanical port |
| Asym Jentzsch applications | ~200-300 | Mechanical port |
| Asym energy levels + mass-gap-pos | ~130 | Mechanical port |
| Lattice Källén-Lehmann variance bound (Fourier route) | ~250-500 | New |
| **TOTAL Layer B1** | **~900-1350** | (vs. earlier estimate 1250-1650) |

Lower than the earlier estimate because:

* No "HS extension" is needed — the general infrastructure exists.
* The Fourier-route Källén-Lehmann is much shorter than the abstract
  spectral-theorem route would be (250-500 vs. 400-800 lines).

Wall-clock per CLAUDE.md heuristic: **~2-4 weeks** for Layer B1 if
treated as a focused port (similar to the UNIT 7 / `asymChaosCutoffDecomposition`
discharge pace).

## File layout

Proposed new files in `Pphi2/AsymTorus/`:

```
AsymTorus/
  AsymL2Operator.lean              -- ports L2Operator.lean to asym slice
  AsymJentzsch.lean                -- ports Jentzsch.lean (asym applications)
  AsymPositivity.lean              -- ports Positivity.lean (energy levels)
  AsymSpectralGap.lean             -- ports SpectralGap.lean (the proved half)
  AsymKallenLehmann.lean           -- NEW: lattice K-L variance bound
```

(Alternative: one combined `AsymTransferOperator.lean` if the per-file
split is overkill given the line counts; defer until execution.)

## Order of attack

If/when execution starts:

1. **Pre-port verification**: confirm the Wick-constant convention
   (option β: `wickConstantAsym`) makes the existing `mulCLM` /
   `convCLM` / `hilbert_schmidt_isCompact` apply cleanly. ~1 day,
   no commits.
2. **Phase 1**: `AsymL2Operator.lean` — define `asymTransferWeight`,
   `asymTransferGaussian`, `asymTransferOperatorCLM`; prove
   `_isSelfAdjoint`, `_isCompact`. ~300-400 lines.
3. **Phase 2**: `AsymJentzsch.lean` — port Jentzsch applications.
   `_positivityImproving`, `_strictly_positive_definite`, ground
   simple, eigenvalues positive. ~200-300 lines.
4. **Phase 3**: `AsymPositivity.lean` + `AsymSpectralGap.lean` —
   energy levels, `asymMassGap`, `asymMassGap_pos`. ~130 lines.
5. **Phase 4** (the new content): `AsymKallenLehmann.lean` —
   Fourier-route variance bound. ~250-500 lines.
6. **Status doc updates** + catalog refresh.

Layer B2 (UV uniformity via chessboard, ~2000-3000 lines) starts after
B1 lands; it can also begin earlier in parallel with the new
`reflection-positivity` repo (TBD).

## Dependencies on other workstreams

* **Independent** of lee-yang Phase 1 (Layer A). Can proceed in parallel.
* **Independent** of `embed_l2_uniform_bound` discharge (upstream).
* **Independent** of OS3/OS2 hypothesis discharges.
* **Shares** the Källén-Lehmann / spectral-resolution machinery with
  any future discharge of the square's open `spectral_gap_uniform`
  axiom — so this work has a built-in upstream payoff even before B2.

## What I am NOT scoping here

* The exact Mathlib API for bounded self-adjoint spectral functional
  calculus (the Fourier-route plan avoids needing it; if Mathlib lands
  the full spectral theorem during this work, we may want to switch
  routes).
* The square's open `spectral_gap_uniform` axiom. That's the
  analogue of Layer B2 in the square track, not B1.
* The interaction with Layer A. Once both lands, Layer C (assembly,
  ~50 lines) glues them.
