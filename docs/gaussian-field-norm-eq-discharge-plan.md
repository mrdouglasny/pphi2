# Plan: discharge the 3 `_norm_eq` axioms in gaussian-field

## Current state

After the false-axiom fix and `CylinderSpacetimeSymmetry` consolidation:
- 1 master axiom `cylinderMassOperator_equivariant` over the structure.
- 3 instance axioms providing `preserves_T_norm` per Euclidean operator:
  - `cylinderMassOperator_spatialTranslation_norm_eq`
  - `cylinderMassOperator_timeTranslation_norm_eq`
  - `cylinderMassOperator_timeReflection_norm_eq`

All four are mathematically true. The 3 `_norm_eq` axioms could in principle be discharged, removing them from the axiom list — but the work is substantial.

## Two paths to discharge

### Path 1 — via abstract `T*T = C` identity (clean, requires L² infrastructure)

The mass operator T satisfies `⟨T f, T g⟩_{ell2'} = ⟨f, C g⟩_{L²(cylinder)}`
where C is the covariance: `C = ∫₀^∞ e^{-tA} dt` (Bochner integral of the heat semigroup).

If we can set this up:
- Prove `⟨T(S f), T(S g)⟩ = ⟨S f, C(S g)⟩_{L²}` (Bochner / GNS pullback identity).
- Prove `S` commutes with C from `S` commutes with `e^{-tA}` (linearity of integration).
- Prove `S` is L²-isometric on `CylinderTestFunction L` (Lebesgue/Haar invariance of translations and reflection on `S¹_L × ℝ`).
- Combine: `⟨S f, C(S g)⟩ = ⟨S f, S(C g)⟩ = ⟨S* S f, C g⟩ = ⟨f, C g⟩` (using L²-iso → S*S = id).
- Setting f = g: `‖T(S f)‖² = ⟨f, C f⟩ = ‖T f‖²`.

**Required infrastructure (not currently present in gaussian-field):**
- Explicit L² inner product on `CylinderTestFunction L` (it's currently a Schwartz-style locally-convex space, not a Hilbert space).
- Bochner integration of the heat semigroup giving the covariance C as a CLM into the L² completion.
- The pullback identity `⟨T f, T g⟩_{ell2'} = ⟨f, C g⟩_{L²}`.

**Estimated cost:** 5–10 active days. Significant new file (`Cylinder/L2Structure.lean` or similar).

### Path 2 — mode-by-mode (no new abstract structure, more proof work)

The mass operator decomposes mode-by-mode:
`(T f)_m = DM_b(R_{ω_a}(slice_a f))` where `m = pair(a, b)`, `R_{ω_a}` is the resolvent multiplier, `slice_a` is the spatial Fourier mode `a`, and `DM_b` is the b-th Dynin–Mityagin / Hermite coefficient.

**For time reflection (`Θ : t ↦ -t`):**
- `slice_a (Θ f) = Θ_t (slice_a f)` (spatial slice commutes with temporal reflection).
- `R_{ω_a} ∘ Θ_t = Θ_t ∘ R_{ω_a}` (resolvent symbol `σ(p) = (p² + ω²)^{-1/2}` is even ⇒ Fourier multiplier commutes with reflection).
- `DM_b(Θ_t g) = (-1)^b DM_b(g)` (Hermite functions: `h_b(-t) = (-1)^b h_b(t)`).

So `(T(Θ f))_m = (-1)^b (T f)_m`, hence `((T(Θ f))_m)² = ((T f)_m)²` and `‖T(Θ f)‖² = ‖T f‖²`.

**For spatial translation (`T_v` on `S¹_L`):**
- `slice_a (T_v f)` is a rotation of `slice_a f` and `slice_{a'} f` over the (cos_a, sin_a) pair (where a' is the conjugate).
- `R_{ω_a}` commutes with this rotation (resolvent symbol is independent of a-direction in Fourier space).
- Squared sum over (a, a') is invariant under rotation.

**For time translation (`T_τ` on ℝ):**
- `slice_a (T_τ f) = T_τ (slice_a f)`.
- `R_{ω_a}` commutes with `T_τ` (Fourier multipliers commute with translation).
- `DM_b(T_τ g)` is some linear combination, but `Σ_b DM_b² = ‖g‖²_{L²}` (Parseval), and `T_τ` preserves L² norm. So `Σ_b DM_b(T_τ g)² = Σ_b DM_b(g)²`.

**Required infrastructure:**
- Theorem: `slice_a (cylinderTimeReflection f) = schwartzReflection (slice_a f)`.
- Theorem: `resolventMultiplierCLM` commutes with `schwartzReflection`.
- Theorem: `DM_b(schwartzReflection g) = (-1)^b DM_b(g)`. (Hermite-parity).
- Analogous for spatial/time translation, plus paired-coeff-product invariance from `SmoothCircle/FourierTranslation.lean`.
- Plancherel for `SmoothMap_Circle` and Schwartz space (the latter is Mathlib's `SchwartzMap.fourier`).

**Estimated cost:** 5–10 active days. ~3 new files (one per operator) or one combined file.

## Key insight (added after the question "is CylinderTestFunction a tensor product?")

**Yes, it is.** `CylinderTestFunction L = NuclearTensorProduct (SmoothMap_Circle L ℝ) (SchwartzMap ℝ ℝ)`,
and each Euclidean operator is `nuclearTensorProduct_mapCLM` of factor operations:

```lean
cylinderSpatialTranslation L v = nuclearTensorProduct_mapCLM (circleTranslation L v) id
cylinderTimeTranslation L τ    = nuclearTensorProduct_mapCLM id (schwartzTranslation τ)
cylinderTimeReflection L       = nuclearTensorProduct_mapCLM id schwartzReflection
```

This **substantially reduces the proof scope** — Path 2 (mode-by-mode) becomes much cleaner because the slice operation factors through the tensor structure.

### Refined proof outline

For **time-direction** operators (`id ⊗ S₂`):
- `ntpSliceSchwartz a((id ⊗ S₂) f) = S₂(ntpSliceSchwartz a f)` — provable by extension from the pure-tensor case `slice_a(g ⊗ h) = coeff_a(g) • h`.
- Resolvent multiplier commutativity:
  - `R_{ω_a} ∘ schwartzReflection = schwartzReflection ∘ R_{ω_a}` (resolvent symbol is even in p).
  - `R_{ω_a} ∘ schwartzTranslation τ = schwartzTranslation τ ∘ R_{ω_a}` (Fourier multipliers commute with translation).
- DM-coefficient transformation:
  - Reflection: `DM_b(reflect g) = (-1)^b DM_b(g)` (Hermite-function parity).
  - Translation: per Parseval, `Σ_b DM_b(translate g)² = ‖translate g‖²_{L²} = ‖g‖²_{L²} = Σ_b DM_b(g)²`.
- Combined per spatial mode `a`, then summed over `a`, gives the result.

For **spatial translation** (`S₁ ⊗ id` with `S₁ = circleTranslation v`):
- The slice transforms as a rotation within paired `(cos_{2k-1}, sin_{2k})` modes (existing theorem `paired_coeff_product_circleTranslation` in `SmoothCircle/FourierTranslation.lean`).
- The resolvent multiplier `R_{ω_a}` depends only on `|k|` (frequency, not parity), so it's the **same** across paired modes — preserving the rotation structure.
- Squared sum over `(2k-1, 2k)` is rotation-invariant: `(cos²θ + sin²θ)·(‖slice_{2k-1}‖² + ‖slice_{2k}‖²) = ‖slice_{2k-1}‖² + ‖slice_{2k}‖²`.

### Revised estimate

- **Time reflection**: ~1-2 days.
- **Time translation**: ~2-3 days (needs Schwartz Plancherel — likely available in Mathlib).
- **Spatial translation**: ~3-5 days (needs the slice-rotation interaction; `paired_coeff_product_circleTranslation` is the key existing input).

**Total: ~6-10 active days, ~1-2 weeks wall-clock.**

## Recommendation

The work is well-defined and tractable now that the tensor structure is recognized. The 3 `_norm_eq` axioms are mathematically true (Gemini-vetted) and the proofs follow a consistent pattern: slice commutativity → resolvent commutativity → squared-sum invariance.

Time reflection is the simplest entry point — it could be discharged in a focused 1-2 day effort, providing a template for the other two.

If/when this becomes a priority, **start with time reflection**, validate the pattern, then apply to time translation and spatial translation.

## Status

- **Audit:** all 4 axioms in `Cylinder/GreenFunction.lean` are mathematically true; the previous 1-axiom version was false.
- **Pphi2:** unaffected (19 axioms, 0 sorries).
- **Gaussian-field:** 9 axioms total (was 6 with 1 false; now 9 all true).
- **Net work for full discharge:** ~5–10 active days, ~1–2 weeks wall-clock.
