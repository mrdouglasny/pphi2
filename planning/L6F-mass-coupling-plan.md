# L6F endgame — large-mass weak coupling (the last step of the discharge)

> ⛔ **SUBSUMED by Route A (2026-06-07) — do not pursue this large-mass endgame.** Non-Gaussianity on
> T² is now proved **axiom-free** by Route A (`torus_pphi2_isInteractingStrict_weakCoupling`,
> `TorusContinuumLimit/TorusCouplingResult.lean`), which does **not** use
> `torus_weakCoupling_lattice_connectedFourPoint_strictNeg` and does **not** need the large-mass step
> this doc plans — it reused `lattice_u4_neg_uniform` directly via a coupling-family continuum limit +
> 4-homogeneity. The `λ=1` normalization is Route B (continuum dilation), DEFERRED
> (`continuum-rescaling-plan.md`). Kept for the record. See `route-A-weak-coupling-plan.md`.

Branch `l5-affine-bound`. After L3 + L5 + the L6F **reduction**, the headline axiom
`torus_weakCoupling_lattice_connectedFourPoint_strictNeg` reduces (axiom-clean) to a single
inequality. This doc plans the one remaining step.

> **2026-06 correction (Gemini deep-think review).** An earlier draft of this plan proposed a
> "mass↔coupling field redefinition" with `g = 1/(4 mass²)`. **That is wrong.** On a *fixed* lattice
> you cannot map a mass-`m` GFF to a reference-mass GFF by a scalar field rescaling `ω↦c•ω`: the
> kinetic term `−Δ_a` and the mass term `m²` scale differently, so `c²(−Δ_a+m²)⁻¹ ≠ (−Δ_a+m₀²)⁻¹`
> for any scalar `c`. The continuum relation `g∝λ/m²` relies on rescaling *space*, impossible on a
> frozen lattice; the lattice effective coupling is `∝1/m⁴`, and the `1/4` was a convention red
> herring. The correct route is **direct large-mass**, below — it needs **no field redefinition and
> no Minlos/Cramér–Wold axiom**, and reuses the existing `lattice_u4_neg_uniform` machinery verbatim.

## What is already proven (axiom-clean)

`torusConnectedFourPoint_eq_u4_one` (`TorusU4Pullback.lean`): the discharge ≡
```
(★)  ∃ m₀ > 0, ∀ mass > m₀, ∃ (f) (c), 0 < c ∧
       ∀ N [NeZero N], u4 2 N (circleSpacing L N) mass … P (latticeTestFn L N f) 1 ≤ -c.
```
`lattice_u4_neg_uniform` (`U4AffineBound.lean`): for `f_c` = normalised constant,
`∃ g c > 0, ∀N, u4_N(g) ≤ -c` at `g₀ = min 1 (s/(2K))`, `s = 6(L⁶ mass⁸)⁻¹` (uniform leading slope),
`K` = uniform `|u₄''|` bound. Its core (`deriv_affine_bound_neg_of_continuousOn` at any
`g ≤ s/(2K)`, with `u4_at_zero`/`u4_continuousOn`/`u4_hasDerivAt`/the affine bound) evaluates `u₄` at
**any** `g ≤ s/(2K)`, not just `g₀`.

## The key observation
`(★)` needs `u₄` at the FULL coupling `g=1`. The affine machinery gives `u₄(g) ≤ -(s/2)g` for
`g ≤ s/(2K)`. **So `u₄(1) ≤ -(s/2) < 0` as soon as `s/(2K) ≥ 1`, i.e. `s(mass) ≥ 2 K(mass)`.**

Now track the `mass`-dependence:
- `s(mass) = 6 (L⁶ mass⁸)⁻¹` — already EXACT (`leadingTerm_const_eq` + `torus_volume_eq`); `~ mass⁻⁸`.
- `K(mass)` (the `|u₄''|` bound) `→ 0` *faster* than `mass⁻⁸` as `mass→∞`: every Gibbs moment
  `⟨(ωf)^a V^b⟩` in the `u₄''` expansion carries factors of the covariance `C_mass`, and
  `‖C_mass‖_op ≤ mass⁻²` (since `−Δ_a ⪰ 0` ⟹ `(−Δ_a+mass²)⁻¹ ⪯ mass⁻²·I`). Gemini's diagram count:
  `u₄'' = ⟨φ(f)⁴; V; V⟩_c` has 4 external + 8 vertex fields = 12, fully contracted by 6 propagators,
  so `|u₄''| ≤ K' · mass⁻¹⁰` (a strictly higher power of `1/mass` than the `mass⁻⁸` slope; the
  precise power may be `mass⁻¹⁰`…`mass⁻¹²` depending on how the lattice sums are bounded — only
  `K(mass) = o(mass⁻⁸)` is needed).

Hence `s(mass)/(2K(mass)) ~ mass²·const → ∞`, so for `mass > m₀` (some explicit threshold)
`s(mass) ≥ 2K(mass)`, giving `g₀ = min 1 (s/2K) = 1` and `u₄(1,mass) ≤ -(s/2) < 0`. Done.

## Remaining work (concrete, no new axioms)
1. **Covariance operator bound** `‖C_mass‖_op ≤ mass⁻²` — ✅ **DONE**. `massEigenvalues_ge_mass_sq`
   (`mass² ≤ λ_k`, `−Δ_a` PSD) and `covariance_inner_le_mass_inv_sq_norm_sq` (`⟨Tg,Tg⟩ ≤ mass⁻²∑g²`)
   already existed; surfaced as `lattice_second_moment_le_mass_inv`
   (`TorusPropagatorConvergence.lean`): `∫(ωg)² dμ_GFF ≤ (a^d)⁻¹·mass⁻²·∑_x g(x)²` (uniform in `g`,
   modulo the GJ volume factor). This is the field-side `mass⁻²` decay the moment bounds consume.
   Axiom-clean.
   - ✅ **Pointwise** version: `gffPositionCovariance_abs_le_mass_inv`
     (`CovariancePointwiseBound.lean`): `|gffPositionCovariance x y| ≤ (a²)⁻¹·mass⁻²` (diagonal bound
     + Cauchy–Schwarz). The atomic input for the V-moment covariance double-sums.
2. **`mass`-quantitative `∫V²`** (the next wall, the bulk): mass-grade `interaction_variance_le`
   to `∫V² ≤ C·mass⁻⁸` (or any `o(mass⁻⁸)`) by threading `gffPositionCovariance_abs_le_mass_inv`
   through the L1 covariance double-sums (`canonicalSmoothCovariance_pow_double_sum_le`,
   `rough_error_variance` — `⟨V²⟩ ~ a^{2d}∑_{x,y} C(x,y)⁴`, each `C` factor `~mass⁻²`; mind the
   `a^d·#sites = L^d` volume bookkeeping so the constant stays `N`-uniform). Then `∫V^{2m} ≤
   Cb·(∫V²)^m` (chaos, `interaction_moment_le`, mass-independent `Cb`) gives all V-moments graded,
   and the L3 free products `∫(ωf)^{2n}V^{2k}` + `K(mass) = O(mass⁻¹⁰)` follow by composition with
   item 1. (Field moments already graded by item 1; `√K_Nelson → 1` as `mass→∞` since `V→0`.)
3. **Threshold + assembly**: pick `m₀` with `s(mass) ≥ 2K(mass)` for `mass>m₀`; instantiate the
   affine-bound core at `g=1` (`g₀=1`, `hKg : K·1 ≤ s/2`); combine with
   `torusConnectedFourPoint_eq_u4_one` ⟹ `(★)` ⟹ discharge. Also need the test-function match:
   the discharge's `f` should be a `TorusTestFunction` whose `latticeTestFn L N f = f_c` (the constant
   torus function ↦ the normalised constant lattice field) — a small lemma.

## Optional alternative (Route 2, for the record)
Gemini's corrected field redefinition `φ = mass⁻¹ψ` maps `μ_{GFF,mass}` to a Gaussian with covariance
`C_ψ = (I − mass⁻²Δ_a)⁻¹ → I`, coupling `g = mass⁻⁴`, and `u₄^φ = mass⁻⁴ U(mass⁻⁴, C_ψ)`. Clean, but
it STILL needs the field-rescale→pushforward measure identity (the deferred Minlos fact). **Route 1
is preferred precisely because it avoids that.**

## Honest scope
The hard analysis (L3 + all of L5 + the L6F reduction) is proven and axiom-clean. The remainder is a
`mass`-quantitative refinement of bounds already in hand (covariance decay + graded moment bounds) +
a threshold assembly — concrete real-analysis, no new axioms, a few focused sessions. Item 2 (graded
`u₄''` bound) is the bulk.
