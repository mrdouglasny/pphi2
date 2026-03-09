# Proof Guide: `fourier_representation_convolution`

## Status

**`inner_convCLM_pos_of_fourier_pos` is PROVED** as a theorem, using the
Fourier representation axiom + `fourier_gaussian_pos` + Plancherel injectivity.

The remaining axiom is `fourier_representation_convolution` (private, in
`GaussianFourier.lean`).

## The axiom to prove

In `Pphi2/TransferMatrix/GaussianFourier.lean`:

```lean
private axiom fourier_representation_convolution
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume)
    (hg_cont : Continuous g) (f : L2SpatialField Ns) :
    @inner ℝ _ _ f (convCLM g hg f) =
    ∫ w : EuclideanSpace ℝ (Fin Ns),
      (gHat Ns g w).re *
      ‖(fHat Ns f : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) w‖ ^ 2
```

**In words:** The Fourier representation of the convolution quadratic form:
`⟨f, g⋆f⟩_ℝ = ∫ Re(ĝ_ℂ(w)) · ‖f̂_ℂ(w)‖² dw`.

**Verification:** Standard result in Fourier analysis. See Folland §8.3,
Reed-Simon I §IX.4.

## Type system context

- `SpatialField Ns = Fin Ns → ℝ` — plain pi type, NO inner product
- `EuclideanSpace ℝ (Fin Ns) = PiLp 2 (fun _ => ℝ)` — HAS `InnerProductSpace ℝ`
- `WithLp.equiv 2 _ : EuclideanSpace ℝ (Fin Ns) ≃ (Fin Ns → ℝ)` bridges the two
- `L2SpatialField Ns = Lp ℝ 2 (volume : Measure (SpatialField Ns))` — ℝ-valued L²
- `convCLM g hg : L2SpatialField Ns →L[ℝ] L2SpatialField Ns` — convolution CLM
  defined in `Pphi2/TransferMatrix/L2Convolution.lean`
- The L² Fourier transform `Lp.fourierTransformₗᵢ` acts on **ℂ-valued** L²:
  `Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2`
- The measures on `SpatialField Ns` and `EuclideanSpace ℝ (Fin Ns)` are the same
  Lebesgue measure (WithLp.equiv is measure-preserving)

## Mathematical proof

The proof has three phases.

### Phase A: The Fourier representation identity

For all f ∈ L²(ℝⁿ, ℝ):

```
⟨f, g⋆f⟩_ℝ = ∫ Re(ĝ_ℂ(k)) · |f̂_ℂ(k)|² dk
```

**Derivation:**
1. Embed f as ℂ-valued: f_ℂ(x) = (f(x) : ℂ)
2. ⟨f, g⋆f⟩_ℝ = Re(⟨f_ℂ, (g⋆f)_ℂ⟩_ℂ)
3. By Plancherel: = Re(⟨f̂_ℂ, (g⊛f)̂_ℂ⟩_ℂ)
4. By convolution theorem: (g⊛f)̂_ℂ = ĝ_ℂ · f̂_ℂ
5. So = Re(∫ f̂_ℂ(k) · conj(ĝ_ℂ(k) · f̂_ℂ(k)) dk)
   = Re(∫ conj(ĝ_ℂ(k)) · |f̂_ℂ(k)|² dk)
   = ∫ Re(ĝ_ℂ(k)) · |f̂_ℂ(k)|² dk

(The last step: Re commutes with integral, and Re(conj(z) · r) = Re(z) · r
for real r ≥ 0.)

### Phase B: Strict positivity

Given the identity:
- Re(ĝ_ℂ(k)) > 0 for all k (hypothesis)
- |f̂_ℂ(k)|² ≥ 0 for all k
- f ≠ 0 implies f̂_ℂ ≠ 0 in L² (Plancherel injectivity), so |f̂_ℂ|² > 0 on a
  set of positive measure
- Therefore ∫ Re(ĝ_ℂ(k)) · |f̂_ℂ(k)|² dk > 0

## What was done (Option 2 from original guide)

The original `inner_convCLM_pos_of_fourier_pos` axiom was decomposed:

1. **`fourier_representation_convolution`** — Fourier representation identity (axiom)
2. **`fourier_ae_nonzero_of_nonzero`** — Plancherel injectivity (proved)
3. **`toEuclideanComplexL2_ne_zero`** — R→C embedding injectivity (proved)
4. **`inner_convCLM_pos_of_fourier_pos`** — Strict positivity (proved from above)

The only remaining axiom is `fourier_representation_convolution`.

## Strategy to prove the remaining axiom

### Schwartz density via `DenseRange.equalizer` (~300-500 lines)

**Step 1:** Show LHS `f ↦ ⟨f, Conv_g f⟩` is continuous on L²
(already proved as `convQuadForm_continuous`).

**Step 2:** Show RHS `f ↦ ∫ Re(ĝ_ℂ(k)) · ‖f̂_ℂ(k)‖² dk` is continuous on L².
Argument: `|Re(ĝ)| ≤ ‖g‖₁` (bounded), Fourier is isometry, so
`|Q(f₁) - Q(f₂)| ≤ ‖g‖₁ · (‖f₁‖ + ‖f₂‖) · ‖f₁ - f₂‖`.

**Step 3:** For Schwartz `s`, prove the identity using:
- `Real.fourier_smul_convolution_eq` (convolution theorem for integrable+continuous)
- `SchwartzMap.integral_sesq_fourier_fourier` (Parseval for Schwartz)

**Step 4:** Apply `DenseRange.equalizer` with `SchwartzMap.denseRange_toLpCLM`.

**Main blocker:** The L² convolution theorem is not yet in Mathlib. The
Schwartz density approach works because the convolution theorem IS available
for integrable+continuous functions (`Real.fourier_smul_convolution_eq`).
The density argument extends this to L². Formalizing this requires ~300+ lines
of type-theoretic plumbing between SpatialField, EuclideanSpace, real L², and
complex L².

## Available Mathlib API

### Fourier transform on L²
| Theorem | Location | What it gives |
|---------|----------|---------------|
| `Lp.fourierTransformₗᵢ` | `Analysis.Fourier.LpSpace:49` | L² Fourier as `≃ₗᵢ[ℂ]` |
| `Lp.norm_fourier_eq` | `Analysis.Fourier.LpSpace:88` | `‖𝓕f‖ = ‖f‖` on L² |
| `Lp.inner_fourier_eq` | `Analysis.Fourier.LpSpace:92` | `⟪𝓕f, 𝓕g⟫ = ⟪f, g⟫` on L² |
| `SchwartzMap.toLp_fourier_eq` | `Analysis.Fourier.LpSpace:98` | `𝓕(s.toLp 2) = (𝓕s).toLp 2` |

### Schwartz space
| Theorem | Location | What it gives |
|---------|----------|---------------|
| `SchwartzMap.denseRange_toLpCLM` | `SchwartzSpace/Basic.lean:1280` | Schwartz dense in Lp |
| `SchwartzMap.fourier_convolution` | `Fourier/Convolution.lean:191` | `𝓕(f⋆g) = 𝓕f · 𝓕g` on 𝓢 |
| `SchwartzMap.integral_sesq_fourier_fourier` | `SchwartzSpace/Fourier.lean:292` | General sesquilinear Plancherel |
| `SchwartzMap.integral_inner_fourier_fourier` | `SchwartzSpace/Fourier.lean:303` | `∫ ⟪𝓕f, 𝓕g⟫ = ∫ ⟪f, g⟫` |

### Convolution theorem (requires Integrable + Continuous)
| Theorem | Location | What it gives |
|---------|----------|---------------|
| `Real.fourier_mul_convolution_eq` | `Fourier/Convolution.lean:149` | `𝓕(f⋆g) = 𝓕f · 𝓕g` for L¹∩C |
| `Real.fourier_bilin_convolution_eq` | `Fourier/Convolution.lean:103` | Bilinear version |

### Already proved in the project
| Theorem | File | What it gives |
|---------|------|---------------|
| `convCLM` | `L2Convolution.lean:352` | Convolution CLM on L² |
| `convCLM_spec` | `L2Convolution.lean:398` | Pointwise: `(Conv_g f)(x) = ∫ g(t)f(x-t) dt` a.e. |
| `convCLM_isSelfAdjoint_of_even` | `L2Convolution.lean:595` | Self-adjoint for even g |
| `integral_mul_conv_eq` | `L2Convolution.lean:417` | Fubini: `∫ h(g⋆f) = ∫ (g⋆h)f` |
| `young_convolution_memLp` | `L2Convolution.lean:241` | g ∈ L¹, f ∈ L² → g⋆f ∈ L² |
| `young_convolution_bound` | `L2Convolution.lean:259` | `‖g⋆f‖₂ ≤ ‖g‖₁ · ‖f‖₂` |
| `fourier_gaussian_pos` | `GaussianFourier.lean:34` | `Re(𝓕(exp(-b‖·‖²))) > 0` |

## Key technical pitfalls

1. **ℝ vs ℂ L²:** Our `L2SpatialField Ns` is `Lp ℝ 2 volume` (ℝ-valued).
   Mathlib's Fourier isometry is on `Lp ℂ 2 volume` (ℂ-valued). You need an
   embedding CLM `L²(ℝ) → L²(ℂ)` via `ofReal`. This does not exist ready-made
   in Mathlib — you'll need to construct it (or axiomatize it).

2. **SpatialField vs EuclideanSpace:** The Fourier transform needs
   `InnerProductSpace ℝ V` for the kernel `exp(-2πi⟨v,w⟩)`. Our L² lives on
   `SpatialField Ns = Fin Ns → ℝ` which lacks this. The axiom uses
   `EuclideanSpace ℝ (Fin Ns)` in the Fourier hypothesis and `WithLp.equiv`
   to bridge. Any proof must respect this — you can't just apply `Lp.inner_fourier_eq`
   directly on `L2SpatialField Ns`.

3. **Convolution theorem requires Continuous + Integrable:** The Mathlib theorem
   `Real.fourier_mul_convolution_eq` requires BOTH `Integrable` AND `Continuous`.
   General L¹ functions aren't continuous. Schwartz functions are, so the Schwartz
   route works. Alternatively, approximate g by continuous L¹ functions.

4. **Schwartz density scalar field:** `SchwartzMap.denseRange_toLpCLM` gives
   density over `ℝ`, but `Lp.fourierTransformₗᵢ` is over `ℂ`. You need to
   check that `denseRange_toLpCLM ℂ` also works (it should, since `ℝ ⊆ ℂ`).

5. **Measure conventions:** Make sure `volume` on `SpatialField Ns` and on
   `EuclideanSpace ℝ (Fin Ns)` are identified. `WithLp.equiv` is a
   `MeasurePreserving` equivalence, so this should be fine, but you may need
   to explicitly invoke `MeasurePreserving.integral_comp` or similar.

6. **Fourier convention:** Mathlib uses `𝓕f(w) = ∫ f(v) exp(-2πi⟨v,w⟩) dv`.
   This gives the clean convolution theorem `𝓕(f⋆g) = 𝓕f · 𝓕g` and Plancherel
   `⟨f,g⟩ = ⟨𝓕f, 𝓕g⟩` with no normalization constants.

## Project conventions

- After proving, change `private axiom` to `private theorem` in GaussianFourier.lean
- Run `lake build` to verify the full project compiles
- Run `./scripts/count_axioms.sh` to confirm axiom count decreased
- Update `status.md`, `README.md` with new counts
- All downstream theorems (`inner_convCLM_pos_of_fourier_pos`,
  `gaussian_conv_strictlyPD`, spectral gap) are already proved and will
  continue to work once the axiom becomes a theorem

## Build and test

```bash
# Build just this file (fast iteration)
lake env lean Pphi2/TransferMatrix/GaussianFourier.lean

# Full project build
lake build

# Check axiom count
./scripts/count_axioms.sh
```

## References

- Folland, *Real Analysis*, §8.3 (Fourier analysis on ℝⁿ)
- Reed-Simon I, §IX.4 (Fourier transform on L²)
- Rudin, *Functional Analysis*, Ch. 1 (Positive definite functions)
- Stein-Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Ch. 1
