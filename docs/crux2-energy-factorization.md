# Crux-2: the energy/density factorization (derivation, vetted before formalizing)

**Status: derivation complete and vetted (Gemini deep-think, 2026-06-04). Not yet formalized.**

The Layer-B2 measure↔operator bridge needs: *the slice-pushforward of the interacting lattice
measure equals the periodic path measure of the transfer kernel `k`.* This note records the
exact `a`-power bookkeeping — the place the B5 docstring warns is "essential — a naive bound is
`a`-non-uniform and WRONG" — derived on paper and vetted, so the formalization target is pinned
correctly (a factor-of-`a` error here would make the target statement false).

## Result (the target)

Through the slice identification `φ ↔ (ψ_t)_{t∈ZMod Nt}` (`asymSliceEquiv`),

```
dμ_int/dλ  =  (1/Z) · ∏_{t∈ZMod Nt} k(ψ_t, ψ_{t+1})     EXACTLY,
```

i.e. `(interactingLatticeMeasureAsym).map (sliceEquiv-pushforward) = asymTransferSystem.pathMeasure Nt`
as **normalized probability measures, with no residual `a`-rescaling**. The `1/a` cancellation
that B5 needs lives entirely in the **torus↔lattice test-function map** (`asymLatticeTestFnIso
= a • evalAtSite`), *not* in this factorization.

## The factors of `a` (each one checked independently)

Definitions (verbatim): `Q = massOperatorAsym = −Δ_a + m²`, `(Δ_a φ)(x) = a⁻²(φ(x+e1)+φ(x−e1)+
φ(x+e2)+φ(x−e2)−4φ(x))`; `spatialKinetic ψ = ½Σ_s a⁻²(ψ(s+1)−ψ(s))²`; `spatialPotential ψ =
Σ_s(½m²ψ(s)² + :P:(ψ(s)))`; `timeCoupling ψ ψ' = ½Σ_s(ψ(s)−ψ'(s))²`; transfer weight `w(ψ) =
exp(−(a²/2)·spatialAction ψ)`; transfer Gaussian `G(ξ) = exp(−timeCoupling 0 ξ)`; kernel
`k(x,y) = w(x)·G(x−y)·w(y)`.

**The pivotal point — the covariance square-root convention.** `GaussianField.covariance T f g
= ⟨T f, T g⟩` (Construction.lean:101), so the supplied operator `T` is the *square root* /
factorization operator, and the actual covariance bilinear form is `f ↦ ‖Tf‖²`. Here
`T = latticeCovarianceAsymGJ = a⁻¹ · Q^{−1/2}` (AsymCovariance.lean: docstring "`T = Q^{−1/2}`",
times the `a⁻¹` GJ cell-area normalization). Hence:

```
free covariance form = ‖a⁻¹ Q^{−1/2} f‖² = a⁻² ⟨f, Q⁻¹ f⟩    ⟹   precision = a² Q
```

**(Watch out:** reading `T` as `Q⁻¹` instead of the square-root `Q^{−1/2}` gives precision `aQ`
and a spurious factor-of-`a` mismatch. The square-root squares the `a⁻¹` to `a⁻²`.)**

Slice translations (periodic SBP):
```
Σ_x(φ(x+e1)−φ(x))² = Σ_t Σ_s(ψ_{t+1}(s)−ψ_t(s))² = 2 Σ_t timeCoupling(ψ_t,ψ_{t+1})
Σ_x(φ(x+e2)−φ(x))² = Σ_t Σ_s(ψ_t(s+1)−ψ_t(s))²   = 2 a² Σ_t spatialKinetic(ψ_t)
Σ_x φ(x)²          = Σ_t ‖ψ_t‖²
```

Free measure exponent (precision `a²Q`):
```
½⟨φ, a²Q φ⟩ = (a²/2)⟨φ,Qφ⟩ = (a²/2)[a⁻²(2Σtc + 2a²Σsk) + m²Σ‖ψ_t‖²]
            = Σ_t tc + a²Σ_t sk + (a²/2)m²Σ_t‖ψ_t‖²
interaction:  V_int = a²·Σ_x :P: = a²Σ_t Σ_s :P:(ψ_t(s))    (interactionFunctionalAsym: explicit a²)
```
Kernel exponent:
```
−log ∏_t k = Σ_t tc + a²Σ_t spatialAction(ψ_t)
           = Σ_t tc + a²Σ_t sk + (a²/2)m²Σ_t‖ψ_t‖² + a²Σ_t Σ_s :P:
```
| term | measure | kernel |
|---|---|---|
| timeCoupling | `1` | `1` |
| spatialKinetic | `a²` | `a²` |
| mass `½m²‖·‖²` | `a²` | `a²` |
| interaction `:P:` | `a²` | `a²` |

**Identical term-by-term.** The `a²/2` weight cancels the `a⁻²` in `Δ_a` to give coefficient `1`
on `timeCoupling` — which is correct: in `d` spacetime dimensions the time-difference coefficient
is `a^{d−2}`, and `d=2` ⟹ `a⁰=1` (the time-step `a` cancels the spatial momentum cell-volume).

## Vetting (Gemini deep-think, 2026-06-04, 3m30s)

"Your derivation is exactly correct, mathematically sound, and physically perfectly consistent…
every single factor of `a` matches identically… EXACT equality of the normalized probability
measures is the correct target, no residual `a`-dependent rescaling." Confirmed no hidden
`a`-factors: (i) slice reindexing Jacobian = 1 (coordinate permutation/reshape); (ii) `Z`
irrelevant for normalized equality (identical integrands ⟹ identical normalized measures);
(iii) Wick constants cancel (same `:P:` evaluated on both sides). The coefficient-`1` on
`timeCoupling` is the standard isotropic Riemann-sum action `S = Σ a²[½(∂_tφ)²+½(∂_xφ)²+½m²φ²+:P:]`
with `T ≈ e^{−aH_spatial}`.

## Formalization roadmap (the Lean target, now that the math is pinned)

1. **SBP slice lemma** — `⟨φ, massOperatorAsym φ⟩ = a⁻²·2Σ_t timeCoupling(ψ_t,ψ_{t+1}) +
   2Σ_t spatialKinetic(ψ_t) + m²Σ_t‖ψ_t‖²` through `asymSliceEquiv` (reuse
   `asym_direction_sum_eq_neg_sq`; split the two directions; `ZMod`→slice translation).
2. **Density identity** — `gaussianDensityAsym(φ)·exp(−V_int) = ∏_t k(ψ_t,ψ_{t+1})` pointwise
   (pure `Real.exp` algebra from step 1 + the definitions). The asym `gaussianDensity` is the
   `exp(−(a²/2)⟨φ,Qφ⟩)` Lebesgue density — needs **crux-1** (port `Density.lean`'s
   `normalizedGaussianDensityMeasure_eq_normalizedQuadraticGaussianMeasure` + `evalMapMeasurableEquiv`
   to the asym lattice) to connect this density to the abstract `GaussianField.measure`.
3. **Measure equality** — combine: `μ_int.map sliceEquiv = pathMeasure` (normalized; Jacobian 1).

So crux-2 step 1 (SBP) and step 2-algebra are local and provable now; the measure-level
conclusion still routes through the crux-1 density-bridge port.
