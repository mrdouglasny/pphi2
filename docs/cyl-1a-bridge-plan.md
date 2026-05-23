# CYL-1a discharge plan — `MeasureHasGreenMomentBound` via finite-dim Boué–Dupuis

*Draft 2026-05-22. How to discharge the cylinder volume-uniform Green-moment input using the
`gibbs-variational` finite-dim Boué–Dupuis bound (now a pinned dependency).*

## Target

`MeasureHasGreenMomentBound Ls mass hmass K C μ` — `Pphi2/AsymTorus/MomentBoundOS1.lean:107`:
for the IR-limit interacting measure `μ` and **every** test function `f`,

```
Integrable (fun ω => exp |ω f|) μ   ∧   ∫ exp |ω f| ∂μ ≤ K · exp (C · G_{Lt,Ls}(f,f))
```

with `G = GaussianField.asymTorusContinuumGreen` (continuum torus propagator,
`gaussian-field/HeatKernel/Bilinear.lean`, spectral sum `Σ_m ĉ_m(f)² / (λ_m + m²)`).
Consumed by `AsymTorusSequenceHasUniformGreenMomentBound` (`IRLimit/IRTightness.lean:48`) →
cylinder tightness + OS0 (`routeBPrime_cylinder_OS`).

## What already exists (from the API map)

- **Interacting measure is a Gibbs tilt of a finite-dim Gaussian.**
  `asymTorusInteractingMeasure = Measure.map (asymTorusEmbedLift) (interactingLatticeMeasure)`
  (`AsymTorus/AsymTorusEmbedding.lean:184`), and
  `interactingLatticeMeasure = Z⁻¹ • (latticeGaussianMeasure).withDensity (exp (−V_a))`
  (`InteractingMeasure/LatticeMeasure.lean:211`), where the base
  `latticeGaussianMeasure = GaussianField.measure (latticeCovarianceGJ …)` lives on the
  **finite-dimensional** `FinLatticeField 2 N = (FinLatticeSites 2 N → ℝ) ≅ ℝ^{N²}`
  (`gaussian-field/Lattice/FiniteField.lean:33`), with covariance `C = a^{−d} Q⁻¹`, `Q = −Δ_a + m²`.
  `V_a = a^d Σ_x :P:(ω(δ_x))` Wick-ordered (`LatticeMeasure.lean:65`, `wickConstant`
  `WickOrdering/Counterterm.lean:66`).
- **Lattice cutoff exp-moment bound** — `AsymTorus/AsymTorusOS.lean:669` (private):
  `∫ exp|ωf| dμ_N ≤ K · exp(σ²_N(f))`, RHS the **lattice second moment / Sobolev seminorm**
  `σ²_N(f) = ∫ (ω g)² dμ_GFF`, `g = asymLatticeTestFn Lt Ls N f`.
- **Nelson uniform estimate** — `AsymTorus/AsymTorusInteractingLimit.lean:69`:
  `∫ (exp(−V_a))² dμ_GFF ≤ K` uniform in `N`.
- **The one axiom on the critical path** — `AsymTorus/AsymTorusOS.lean:852`:
  `asymTorusInteracting_exponentialMomentBound` gives the *limit* measure an exp-moment bound with
  an abstract continuous seminorm `q`, conditional on BC (weak) convergence. Discharging CYL-1a
  means proving `MeasureHasGreenMomentBound` with explicit, uniform `K, C` — superseding this axiom.
- **gibbs-variational** (pinned dep): `GibbsVariational.neg_log_integral_exp_neg_le` (P-C),
  `klDiv_stdGaussian_map_add` (P-B), `integral_le_log_integral_exp_add_klDiv` (P-A) — all on
  `stdGaussian n = Measure.pi (fun _ => gaussianReal 0 1)`.

## The bridge — four steps

### Step 0 — Whitening: `latticeGaussianMeasure ≅ pushforward of stdGaussian` (~80% done upstream)

**Already proved in gaussian-field** — `GaussianField/StandardGaussianBridge.lean:435`:

```
gffOrthonormalProj_pushforward_eq_stdGaussian :
  Measure.map (gffOrthonormalProj d N a mass ha hmass) (latticeGaussianMeasure d N a mass ha hmass)
    = Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1)
```

So the whitening map already exists as `gffOrthonormalProj` (the Gram–Schmidt/orthonormalisation
of the field coordinates; `StandardGaussianBridge.lean:101`), it is **linear and continuous**
(`gffOrthonormalProjCLM : Configuration (FinLatticeField d N) →L[ℝ] (FinLatticeSites d N → ℝ)`,
line 306, with `gffOrthonormalProjCLM_eq`), and its pushforward of the lattice GFF is exactly the
product standard Gaussian — which is `GibbsVariational.stdGaussian` modulo the index type
(`FinLatticeSites d N` vs `Fin (N^d)`). Proof there is via `iIndepFun` + per-coordinate `N(0,1)`
(`gffOrthonormalCoord_normal` / `_independent`). The companion charFun form is
`gffOrthonormalProj_charFun` (line 465).

**Residual (small, new):**
- *(0b) Invertibility.* Package `gffOrthonormalProjCLM` as a `ContinuousLinearEquiv` (the whitening
  of a PD covariance on a finite-dim space is invertible) so that `V_a` and each pairing
  `ω ↦ ω f` factor through it: `V_a = Ṽ ∘ gffOrthonormalProj` with `Ṽ = V_a ∘ proj⁻¹`, and likewise
  the linear functionals. Then `∫ exp(−V_a) dμ_GFF = ∫ exp(−Ṽ) d(stdGaussian)` by `integral_map`,
  so P-A/P-C apply with `V := Ṽ`.
- *(0c) Index match.* Either reindex `FinLatticeSites d N ≃ Fin (N^d)` (`Fintype.equivFin` +
  `Measure.pi_map_piCongrLeft`), **or** — cleaner — generalise `GibbsVariational.stdGaussian` and
  `neg_log_integral_exp_neg_le` from `Fin n` to an arbitrary `Fintype ι`. The latter is nearly free:
  `klDiv_pi` and `klDiv_gaussianReal_shift` are already general/coordinatewise, and P-C only uses
  `Fin n` through `stdGaussian n` and `∑ i, (h i)²`.

*(Alternative/complementary route, also upstream: `GaussianField/Density.lean`'s explicit
massEigenbasis density — `sitePairing_eq_massEigenbasis_sum`,
`normalizedGaussianDensityMeasure_charFunDual_eq_latticeGaussianFieldLaw` (line 1014) — diagonalises
the same covariance and matches the lattice law by `charFunDual` uniqueness.)*

Verify `gffOrthonormalProj_pushforward_eq_stdGaussian` is itself bare-trio (`#print axioms`) when
wiring, since the whole CYL-1a discharge rests on it.

### Step 1 — Partition-function lower bound (free energy), volume-uniform

Apply P-C `neg_log_integral_exp_neg_le (N²) h (V := V_a ∘ W_N⁻¹)`:

```
−log Z_a ≤ ∫ (V_a ∘ W_N⁻¹)(· + h) d(stdGaussian) + ½‖h‖²
```

Choose drift `h` to cancel the leading (Wick-divergent) part of `V_a`, making the RHS **extensive**
(`∝ |Λ| a^d = Vol`), hence `Z_a ≥ exp(−c · Vol)` **uniform in `N`**.
- This is the variational re-derivation of `asymNelson_exponential_estimate` with an explicit,
  drift-controlled constant.
- *Likely simplification in d = 2*: only the log-divergent self-contraction (`wickConstant`) needs
  renormalising, and Wick ordering already absorbs it — so plausibly `h = 0` suffices, giving
  `−log Z_a ≤ ⟨V_a⟩_GFF` (the standard Nelson lower bound). Verify `⟨V_a⟩_GFF` is extensive and
  uniform. (If a nonzero local mean-field `h` is needed, that is the place it enters.)

### Step 2 — Tilted exp-moment (numerator), recovering the cutoff bound with *uniform* `K`

`∫ exp|ωf| dμ_int = Z⁻¹ ∫ exp(|ωf| − V_a) dμ_GFF`.
- Bound the numerator via P-A applied to the linear functional `f = |ω·|` against the tilted
  potential: the Gaussian Laplace transform of a linear functional gives the `exp(c · σ²_N(f))`
  factor (`½ Var`), combined with the Step-1 lower bound on `Z`.
- Net: `∫ exp|ωf| dμ_int ≤ K · exp(C · σ²_N(f))` — the existing `…_cutoff` bound, but now with `K, C`
  **volume-uniform** (the variational argument supplies the missing uniformity).

### Step 3 — UV / Green limit (`σ²_N → G`, pass to the limit measure)

- Covariance convergence: lattice `σ²_N(f) → asymTorusContinuumGreen Ls Lt mass f f` as `N → ∞`
  (relate the `latticeCovarianceGJ` spectral sum to `greenFunctionBilinear`).
- Push the uniform cutoff bound through the BC / weak (Prokhorov) convergence (`ContinuumLimit/`,
  `IRLimit/`) to the limit measure → `MeasureHasGreenMomentBound`. This **discharges the
  `asymTorusInteracting_exponentialMomentBound` axiom** (`AsymTorusOS.lean:852`).

## Sequencing & risk

1. **Step 0 first** — the whitening lemma is the new infrastructure lynchpin; everything downstream
   is a short P-A/P-C application once the lattice GFF is a `stdGaussian` pushforward.
2. Steps 1–2 are then thin wrappers over P-C / P-A on `stdGaussian (N²)`.
3. Step 3 reuses existing UV-limit machinery + one covariance-convergence lemma.

**Open questions.** (a) Does `h = 0` suffice in d = 2 (Wick ordering already cancels the log
divergence)? — verify `⟨V_a⟩_GFF` extensivity. (b) Exactly what does gaussian-field already provide
toward `GaussianField.measure` (finite-dim cov) ↔ `Measure.pi gaussianReal` (the `massEigenbasis`
diagonalization)? (c) The `WeakDual ↔ ℝ^{N²}` coordinate iso carrying `stdGaussian`.

**Why this is worth it.** It replaces the abstract BC-convergence-conditional axiom with a
constructive, volume-uniform bound — no cluster expansion, no stochastic calculus — reusing the
fully-proved (bare-trio) finite-dim Boué–Dupuis stack.
