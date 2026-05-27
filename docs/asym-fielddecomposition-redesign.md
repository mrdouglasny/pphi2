# Heterogeneous `FieldDecomposition` redesign (the §2 bottleneck)

*2026-05-27. Concrete architecture for porting the square polynomial-chaos `CanonicalJoint`
field decomposition (`Pphi2/NelsonEstimate/FieldDecomposition.lean`) to the isotropic
`Z_Nt × Z_Ns` lattice — the dependency-root for discharging `asymChaosCutoffDecomposition` (§2).
Everything in `RoughErrorBound`/`CovarianceBoundsGJ`/`HeatKernelBound` is stated in terms of these
definitions, so this is built first.*

## The square architecture (what we're porting)

`FieldDecomposition.lean` realizes the lattice GFF as the pushforward of a product of two iid
standard-Gaussian families (one for the *smooth* part, one for the *rough* part), synthesized
through the Fourier modes with the cutoff-split covariance weights:

```
CanonicalJoint d N            := ((Fin d → Fin N) → ℝ) × ((Fin d → Fin N) → ℝ)   -- modes = Fin d→Fin N
canonicalJointMeasure         := (Πᵢ N(0,1)) ⊗ (Πᵢ N(0,1))
canonicalEigenvalue m         := (Σ_i latticeEigenvalue1d N a (m i)) + mass²       -- dispersion λ_m
canonicalSmoothWeight m       := exp(-T·λ_m)/λ_m      canonicalRoughWeight m := (1-exp(-T·λ_m))/λ_m
canonicalSmoothModeCoeff x m  := √(smoothWeight m / latticeFourierProductNormSq N d m)
                                   · latticeFourierProductBasisFun N d m x
canonicalSmoothFieldFunction η x := Σ_m smoothModeCoeff x m · η.1 m                 -- synthesize smooth
canonicalRoughFieldFunction  η x := Σ_m roughModeCoeff  x m · η.2 m                 -- synthesize rough
canonicalSumFieldFunction       := smooth + rough
pushforward_eq_GFF : map (φ_S + φ_R) canonicalJointMeasure = latticeGaussianMeasure d N a mass   -- ★
```

The split is exact: `smoothWeight m + roughWeight m = 1/λ_m` = the GFF covariance eigenvalue, and the
two iid families are independent, so the synthesized sum is a centered Gaussian with covariance
`Σ_m (1/λ_m) B_m ⊗ B_m` = the lattice GFF. `★ pushforward_eq_GFF` is the one deep identity; the rest
are definitions + measurability + linearity.

## The heterogeneous analogue (`AsymFieldDecomposition.lean`)

Swap the mode index `(Fin d → Fin N)` → `Fin Nt × Fin Ns` (the rectangular DFT modes, exactly the
index of `abstract_spectral_eq_dft_spectral_2d_asym`), and the product basis → the `Nt`/`Ns` product
of 1D bases. Sites are `AsymLatticeSites Nt Ns = ZMod Nt × ZMod Ns`.

```
AsymCanonicalJoint Nt Ns      := ((Fin Nt × Fin Ns) → ℝ) × ((Fin Nt × Fin Ns) → ℝ)
asymCanonicalJointMeasure     := (Π N(0,1)) ⊗ (Π N(0,1))                  -- over Fin Nt × Fin Ns
asymCanonicalEigenvalue (m₁,m₂) := latticeEigenvalue1d Nt a m₁ + latticeEigenvalue1d Ns a m₂ + mass²
asymCanonicalSmoothWeight m   := exp(-T·λ_m)/λ_m          asymCanonicalRoughWeight m := (1-exp(-T·λ_m))/λ_m
asymBasis (m₁,m₂) x           := latticeFourierBasisFun Nt m₁ x.1 · latticeFourierBasisFun Ns m₂ x.2
asymNormSq (m₁,m₂)            := latticeFourierNormSq Nt m₁ · latticeFourierNormSq Ns m₂
asymCanonicalSmoothModeCoeff x m := √(asymSmoothWeight m / asymNormSq m) · asymBasis m x
asymCanonicalSmoothFieldFunction η x := Σ_m smoothModeCoeff x m · η.1 m       (sum over Fin Nt × Fin Ns)
…rough…, …sum…
asymFieldDecomposition : FieldDecomposition (over AsymLatticeField Nt Ns)     -- the structure instance
  pushforward_eq_GFF : map (φ_S+φ_R) asymCanonicalJointMeasure = latticeGaussianMeasureAsym Nt Ns a mass  -- ★
```

`latticeEigenvalue1d`, `latticeFourierBasisFun`, `latticeFourierNormSq` are the **same** 1D DFT
functions the square uses (per-direction), so no new Fourier objects are needed — just per-direction
`Nt`/`Ns` instead of a `d`-fold product over a single `N`.

## What is MECHANICAL (ports by index-swap)

1. **Measure plumbing** — `AsymCanonicalJoint`, `asymCanonicalJointMeasure`, the
   `…StdGaussianMeasurableEquiv`, `canonicalJointMeasure_map_sum_pi_gaussian`,
   `canonicalJointMeasure_map_stdGaussian`: these are **generic over the mode-index Fintype**
   (`Fintype.card`, `MeasurableEquiv.sumPiEquivProdPi`, `Fintype.equivFin`,
   `measurePreserving_sumPiEquivProdPi_symm`, `GaussianHilbert.stdGaussianFin`). Port = replace
   `CanonicalJointSumIndex d N = (Fin d→Fin N) ⊕ (Fin d→Fin N)` by `(Fin Nt×Fin Ns) ⊕ (Fin Nt×Fin Ns)`.
   Near-verbatim.
2. **Eigenvalue / weights / mode coeffs / synthesis / sum** — direct definitional analogues above.
   The ~90 measurability/linearity/`_eq_of_fst` lemmas (lines 240–400 of the square file) transfer
   with the substitution (they are about finite sums of measurable functions, independent of lattice
   shape).
3. **`latticeFieldToConfig` / `canonicalSmoothConfig` / `canonicalSumConfig`** — the bridge from
   lattice fields to `Configuration`; generic, ports by swapping `FinLatticeField d N` →
   `AsymLatticeField Nt Ns`.

## The ONE deep piece: `★ pushforward_eq_GFF`

`map (φ_S + φ_R) asymCanonicalJointMeasure = latticeGaussianMeasureAsym Nt Ns a mass`.

Proof strategy (reusing Phase-1b):
- `φ_S + φ_R = Σ_m √(1/λ_m)·asymBasis_m · ζ_m` where `ζ_m = η.1 m` (smooth) and `η.2 m` (rough)
  combine: `√smoothWeight·η.1 + √roughWeight·η.2` has variance `smoothWeight+roughWeight = 1/λ_m`
  per mode, i.e. the sum is, in distribution, `Σ_m √(1/λ_m) asymBasis_m · ξ_m` with `ξ_m` iid `N(0,1)`.
- That synthesized field is a centered Gaussian with covariance `Σ_m (1/λ_m) asymBasis_m ⊗ asymBasis_m`,
  which by `abstract_spectral_eq_dft_spectral_2d_asym` (the DFT diagonalization of `Q⁻¹`, Phase 1b)
  is exactly the GJ lattice covariance. So its law is `GaussianField.measure (latticeCovarianceAsymGJ …)
  = latticeGaussianMeasureAsym` (definitional).
- Lean route: match characteristic functionals (`Measure.ext_of_charFun` / the GFF charFun identity),
  OR push through the square's proof structure (`canonicalJointMeasure_map_stdGaussian` →
  `stdGaussianFin` → linear synthesis → `GaussianHilbert` Gaussian-with-given-covariance) — whichever
  the square uses; the only lattice-specific input is the covariance-eigenvalue identity, supplied by
  `abstract_spectral_eq_dft_spectral_2d_asym` + `spectralLatticeCovarianceAsym_inner`.

This is the genuine work (and the schedule risk); the smooth/rough algebra and measure plumbing
around it are mechanical.

## Downstream (after this file)

`RoughErrorBound` / `CovarianceBoundsGJ` / `HeatKernelBound` are stated in terms of
`canonicalEigenvalue`, `canonicalRoughCovariance`, `canonicalSmoothInteraction`, etc. Once the asym
versions of those definitions exist (this file), those files port by substitution: the covariance
sum-bounds become bounds on `Σ_{m} (rough weight)^p` over `Fin Nt × Fin Ns` with the rectangular
dispersion `λ_{m₁,m₂}`, fed by `dft_parseval_2d_asym` + the eigenvalue formula. The smooth lower
bound (`canonicalSmoothInteraction_lower_bound_…`) and the chaos rough-tail
(`canonicalRoughError_…_tail` via the generic `ChaosTailBridge`) transfer near-verbatim. The generic
engine (`bridgeAxiom_of_setup_real_generic`, layer-cake, `ChaosTailBridge`) is reused unchanged.

## Normalization (the GJ prefix — easy to get wrong)

The square `canonicalSmoothFieldFunction` carries a **`(√(a^d))⁻¹` prefix**
(`FieldDecomposition.lean:208`): `φ_S η x = (√(a^d))⁻¹ · Σ_m smoothModeCoeff(x,m)·η.1 m`. This is
exactly the GJ factor of `latticeCovarianceGJ = (√(a^d))⁻¹ • spectral` — without it the synthesis
produces the *bare* spectral covariance, not the GJ one, and `pushforward_eq_GFF` is false. The asym
analogue uses `(√(a²))⁻¹ = 1/a` (d = 2), matching `latticeCovarianceAsymGJ = (√(a²))⁻¹ • spectral`.
**The foundational `asymCanonical{Smooth,Rough}FieldFunction` defs carry this prefix.** The square
records the resulting identity as `canonicalSumFieldFunction_covariance` (covariance =
`(a^d)⁻¹·Σ_m B(x)B(y)/(λ_m·normSq)`) → `canonicalSumFieldFunction_covariance_eq_GJ`.

## Precise `★ pushforward_eq_GFF` route (mirrors the square)

`map (φ_S+φ_R) asymCanonicalJointMeasure = latticeGaussianMeasureAsym` reduces, via **Cramér–Wold**
(`GaussianField.cramerWold`, the route of the square `canonicalSumFieldLaw_eq_latticeGaussianFieldLaw`,
`FieldDecomposition.lean:4161`), to: every site-pairing `⟨f, φ_S+φ_R⟩` has the same Gaussian law as
`⟨f, GFF⟩`. The two pairing-Gaussian lemmas to port:
1. `asymCanonicalSumFieldLaw_pairing_is_gaussian` — `⟨f, φ_S+φ_R⟩` is `N(0, ⟪T_GJ f, T_GJ f⟫)`. The
   synthesis law is the image of a standard Gaussian on `EuclideanSpace` under the synthesis CLM
   (`canonicalStdToFieldCLM` analogue), so it is Gaussian by `ProbabilityTheory.IsGaussian` +
   `IsGaussian.map_eq_gaussianReal`; the variance is `(a²)⁻¹·Σ_m ⟨f,B_m⟩²/(λ_m·normSq)` =
   `⟪T_GJ f, T_GJ f⟫` (smoothWeight+roughWeight = 1/λ — `asymCanonicalSmoothWeight_add_roughWeight`,
   **proved** — times the `(a²)⁻¹` GJ prefix²).
2. `latticeGaussianFieldLaw_asym_pairing_is_gaussian` — `⟨f, GFF⟩` is `N(0, ⟪T_GJ f, T_GJ f⟫)` by
   `GaussianField.pairing_is_gaussian` (generic) + `second_moment_eq_covariance`.
The variances match because `⟪T_GJ f, T_GJ f⟫ = (a²)⁻¹·Σ_m ⟨f,B_m⟩²/(λ_m·normSq)` by
`abstract_spectral_eq_dft_spectral_2d_asym` (Phase 1b) + the `(a²)⁻¹` GJ scaling
(`latticeCovarianceAsymGJ_inner_eq_inv_a_sq_spectral`, **proved** in `AsymWickVariance.lean`).

Remaining infrastructure to port for this: the synthesis CLM (`canonicalStdToFieldCLM` analogue),
the `IsGaussian` instance of its image law, and the `evalMap`/`evalMapInv` config↔field bridge — the
square's `FieldDecomposition.lean:424–4220`. Substantial but well-specified; no new mathematics
(reuses Mathlib `IsGaussian`/`stdGaussian` + `GaussianField.cramerWold`/`pairing_is_gaussian` + the
Phase-1b DFT identity).

## Lean status — `★ pushforward_eq_GFF` is PROVED (2026-05-27)

`Pphi2/NelsonEstimate/AsymFieldDecomposition.lean` (≈1730 lines, 0 axioms, 0 sorries, wired into
`Pphi2.lean`) now contains the full chain through the deep identity:

```
asymCanonicalJointMeasure_map_sumConfig :
  (asymCanonicalJointMeasure Nt Ns).map (asymCanonicalSumConfig …) = latticeGaussianMeasureAsym …
```
`#print axioms = [propext, Classical.choice, Quot.sound]` (verified). The whole square chain was
ported: the synthesis CLM (`asymCanonicalStdToFieldCLM`), its Gaussian law
(`asymCanonicalSumFieldLaw`, `IsGaussian`), the `evalMap`/`evalMapInv` config↔field bridge, the
covariance computation (`asymCanonicalSumFieldFunction_covariance` = `(a²)⁻¹·Σ B/(λ·normSq)`,
`…_covariance_eq_GJ`), the two pairing-Gaussian lemmas, and **Cramér–Wold**
(`asymCanonicalSumFieldLaw_eq_asymLatticeGaussianFieldLaw`).

**This is the §2 bottleneck cleared.** Downstream — `CovarianceBoundsGJ` / `RoughErrorBound` (the
smooth lower bound + rough chaos tail) + `asymChaosCutoffDecomposition` itself — port by
substitution against these definitions, reusing the generic engine (`bridgeAxiom_of_setup_real_generic`,
`ChaosTailBridge`, layer-cake) unchanged.
