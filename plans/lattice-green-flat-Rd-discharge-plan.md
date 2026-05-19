# Discharge plan: `latticeGreenBilinear_basis_tendsto_continuum`

*Plan for discharging the remaining axiom in
`Pphi2/GaussianContinuumLimit/PropagatorConvergence.lean:103` — the
joint-limit propagator-convergence statement that is the analytic core
of the flat-ℝᵈ Gaussian continuum limit. Drafted 2026-05-10.*

## Statement

```lean
axiom latticeGreenBilinear_basis_tendsto_continuum
    (mass : ℝ) (hmass : 0 < mass)
    (a_seq : ℕ → ℝ) (ha_pos : ∀ n, 0 < a_seq n)
    (ha_lim : Tendsto a_seq atTop (nhds 0))
    (N_seq : ℕ → ℕ) [∀ n, NeZero (N_seq n)]
    (hNa : Tendsto (fun n => (N_seq n : ℝ) * a_seq n) atTop atTop)
    (i j : ℕ) :
    Tendsto
      (fun n =>
        latticeGreenBilinear d (N_seq n) (a_seq n) mass
          (DyninMityaginSpace.basis i)
          (DyninMityaginSpace.basis j))
      atTop
      (nhds
        (continuumGreenBilinear d mass
          (DyninMityaginSpace.basis i)
          (DyninMityaginSpace.basis j)))
```

For each pair `(eᵢ, eⱼ)` of multivariate Hermite-function basis vectors
on `ℝᵈ`, as `aₙ → 0` AND `Nₙ aₙ → ∞`:

```
(aₙᵈ)⁻¹ · Σ_{k∈(ℤ/Nₙ)ᵈ} λₖ⁻¹ · ⟨êₖ, ẽᵢ⟩ · ⟨êₖ, ẽⱼ⟩  →  (2π)⁻ᵈ · ∫_{ℝᵈ} eᵢ(k) eⱼ(k) / (‖k‖² + m²) dk
```

Three intertwined limits:
- (UV) `aₙ → 0` — refining the lattice
- (IR) `Lₙ := Nₙ aₙ → ∞` — extending the box
- (Riemann sum) discrete `Σ_k` over `(ℤ/Nₙ)ᵈ` becomes `∫_{ℝᵈ}` measure of size `(2π/Lₙ)ᵈ ↘ 0`

## What's already in hand

### gaussian-field

`gaussian-field/Lattice/Convergence.lean:1121` — **`lattice_green_tendsto_continuum`**:
for any pair `f g : TorusTestFunction L` and fixed `L`, the lattice
covariance on the torus `T²_L` (lattice spacing `a_N = L/(N+1)`) converges
as `N → ∞` to the torus Green's bilinear `greenFunctionBilinear mass hmass f g`.
**Pure UV limit at fixed L.** Proved via:
- `lattice_covariance_pure_eq_2d_spectral` — circulant DFT
- `latticeDFTCoeff1d_quadratic_bound` — `C/(1+m)²` DFT decay
- `latticeEigenvalue1d_tendsto_continuum` — pointwise eigenvalue convergence
- `latticeDFTCoeff1d_tendsto` — pointwise DFT-coefficient convergence
- Tannery on `ℕ × ℕ` with the polynomial bound

This is the heaviest analytic work in the chain, and **it's done**.

### pphi2

`Pphi2/TorusContinuumLimit/TorusPropagatorConvergence.lean:544` —
**`torus_propagator_convergence`**: pphi2-side wrapper for fixed `L`.
Uses gaussian-field's theorem directly after a routine GJ-normalization
cancellation step.

## What the axiom needs that the existing material doesn't provide

Two extra ingredients on top of the torus convergence:

### (I) IR limit: `T_L → ℝᵈ` continuum convergence

For fixed `m > 0` and Schwartz `f, g : ℝᵈ → ℝ`:
```
torusContinuumGreen L mass hmass (periodize_L f) (periodize_L g)  →  continuumGreenBilinear d mass f g
```
as `L → ∞`, where `periodize_L f(x) = Σ_{n ∈ Lℤᵈ} f(x + n)` is the periodization.

This is a **thermodynamic-limit / IR-limit** statement:

```
(2π)⁻ᵈ · L⁻ᵈ · Σ_{n ∈ ℤᵈ} f̂(2πn/L) · ĝ(2πn/L) / ((2πn/L)² + m²)
  →  (2π)⁻ᵈ · ∫_{ℝᵈ} f̂(k) ĝ(k) / (‖k‖² + m²) dk
```

This **is** a Riemann sum — but on a regular momentum lattice with
spacing `2π/L → 0`, integrand bounded by `|f̂(k)| · |ĝ(k)| / m²` which is
integrable (Schwartz × Schwartz / constant). Standard Riemann-sum
convergence for Schwartz functions on `ℝᵈ`. ~200-400 lines if Mathlib
has the right machinery; possibly more if we need to build the
multi-D Riemann sum lemma for Schwartz functions.

Status: **not in either repo**. Would be a natural addition to
gaussian-field as `Lattice/IRLimit.lean` or similar.

### (II) Joint limit `(N, a)` along a sequence with `aₙ → 0`, `Nₙ aₙ → ∞`

Decompose:
```
B(aₙ, Nₙ; f, g) = B(aₙ, Nₙ; f, g) - B^cont_torus(Lₙ; f̃ₙ, g̃ₙ)   [fixed-L UV error]
                + B^cont_torus(Lₙ; f̃ₙ, g̃ₙ) - B^cont_flat(f, g)  [IR error]
                + B^cont_flat(f, g)
```

where `f̃ₙ` is the periodization of `f` to torus `T_{Lₙ}`. Both error
terms tend to zero by (I) and the fixed-L torus convergence,
respectively, **provided** we have uniformity:

- For the UV error: gaussian-field's `lattice_green_tendsto_continuum`
  needs to give a rate that doesn't blow up as `L → ∞`. The proof goes
  through Tannery's theorem with a uniform DFT bound; this bound IS
  uniform in `L` (the bound is `C/(1+m)²` independent of `L`) but
  the *finite-sum truncation* threshold may grow with `L`. Needs check.
- For the IR error: just uses (I).

### (III) Schwartz f vs torus periodic f̃

The axiom's test functions are `ContinuumTestFunction d = SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ`
(flat-ℝᵈ Schwartz). The gaussian-field theorem's test functions are
`TorusTestFunction L` (smooth periodic on `T_L`). Bridge: periodize
Schwartz to torus via `f̃_L(x) = Σ_{n ∈ Lℤᵈ} f(x + n)`. Standard fact
that the periodization is `C^∞` periodic and converges to `f`
appropriately as `L → ∞`. Already used implicitly in
`gaussian-field/Cylinder/MethodOfImages.lean`.

## Three discharge strategies

### Strategy A — Factor through torus + IR limit (~2-3 weeks)

1. Build `gaussian-field/Lattice/IRLimit.lean` proving (I) — torus
   continuum Green's bilinear converges to flat-ℝᵈ Green's bilinear
   as `L → ∞`. ~1-2 weeks.
2. Build the periodization bridge (III) — given Schwartz `f`, produce
   `TorusTestFunction L` and prove its DM-coefficient decay matches.
   ~3-5 days. Likely some of this already exists in
   `Cylinder/MethodOfImages.lean`.
3. Combine via the joint-limit decomposition (II): show the UV error
   from `torus_propagator_convergence` is uniform in `L`, then sum
   with the IR error from step 1. ~1 week.
4. Wire into `latticeGreenBilinear_basis_tendsto_continuum`
   replacement. ~3 days.

**Risk:** the uniformity-in-L of `lattice_green_tendsto_continuum` may
need a re-derivation. The current Tannery argument may have an
implicit L-dependent threshold.

### Strategy B — Direct DCT on momentum representation (~3-4 weeks)

Skip the torus factoring. Express both sides directly in momentum
space:
- Lattice side: `(aₙᵈ)⁻¹ · Σ_{k ∈ (ℤ/Nₙ)ᵈ} (lattice propagator)_k · (lattice DFT of eᵢ)_k · (lattice DFT of eⱼ)_k`. Map to physical momentum `kphys = 2πk/(Nₙaₙ)` and rewrite as a Riemann sum on a refining-and-extending grid.
- Continuum side: `(2π)⁻ᵈ ∫_{ℝᵈ} (continuum propagator)(k) · ê_α(k) · ê_β(k) dk`.
- Apply DCT with dominator `|ê_α(k)| · |ê_β(k)| / m²`.

This is a single direct argument but builds on multi-D Riemann-sum
machinery that Mathlib doesn't yet have. May require new infrastructure.

**Risk:** building multi-D Riemann sums on a refining-AND-extending
grid from scratch is the most analytically delicate part. Possible
~1-2 week sub-project just for the infrastructure.

### Strategy C — Prove the special case d = 2, m > 0 only (~2 weeks)

The axiom is only consumed by pphi2N's d = 2 work (P(φ)₂). Specialize:
- Use d = 2 throughout, don't bother with general dimension.
- Use Strategy A but with d = 2 specific simplifications (Cauchy-Schwarz on
  `Σ |f̂(2πn/L)|² · 1/(...)` works directly without dimension induction).

Same risk profile as A but smaller code surface. Best speed-to-discharge
ratio.

## Recommended path

**Strategy A**, with a sub-decision after step 1:

1. **Stage 1 (~1-2 weeks):** Build `gaussian-field/Lattice/IRLimit.lean`
   — torus continuum Green's bilinear → flat ℝᵈ Green's bilinear as
   `L → ∞`. Verify uniformity-in-L of the existing torus convergence
   proof. **At end of Stage 1, reassess** before committing to (II/III).
2. **Stage 2 (~3-5 days):** Periodization bridge
   `ContinuumTestFunction d → TorusTestFunction Lₙ` with DM-coefficient
   decay matching.
3. **Stage 3 (~1 week):** Joint-limit decomposition + cleanup.

Expected total: **~3 weeks of focused work**, single-file additions to
gaussian-field + pphi2.

## Cross-check with existing work

The user's intuition that "we already have this for the torus continuum
limit" is **half right**: the torus version IS proved
(`lattice_green_tendsto_continuum` in gaussian-field;
`torus_propagator_convergence` in pphi2). What's missing is the flat-ℝᵈ
extension, which needs an IR limit on top of the existing UV limit.

The IR limit (Stage 1 above) is genuinely new analytic content, but
it's a "standard Riemann-sum-for-Schwartz-functions" theorem rather
than the "moving-target Riemann sum" that the original axiom directly
asks for. The factoring trick converts the multi-D refining-and-
extending Riemann sum into a refining-only sequence + an extending-only
sequence, both of which are tractable separately.

## Reusable infrastructure produced

If this discharge succeeds, the following pieces become reusable for
other projects:

- **`gaussian-field/Lattice/IRLimit.lean`** — generic IR-limit
  machinery for the GFF on `T_L → ℝᵈ`. Useful for OSforGFF,
  brownian-motion (cylindrical processes), and any other library
  needing flat-ℝᵈ Schwartz consumers of torus-defined Gaussian fields.
- **Periodization-with-DM-decay bridge** — useful for any cylinder /
  reflection-positivity argument that wants to go from periodic to
  flat space cleanly.
- **The uniform-in-L torus convergence** (if it falls out of Stage 1)
  is itself a reusable tool — currently no other consumer depends on
  it but it would simplify some pphi2 IR-tightness arguments.

## References

- S. Albeverio, S. Mazzucchi, *Mathematical Theory of Feynman Path Integrals*, LNM 523 (2008): periodization machinery.
- J. Glimm, A. Jaffe, *Quantum Physics*, §6.1: torus → ℝᵈ limit for the free scalar.
- B. Simon, *The P(φ)₂ Euclidean QFT*, Ch. I.
- C. Borgs, E. Fremlin, "Joint limits and uniformity for Riemann sums" (note: speculative reference, the theorem is folklore).
