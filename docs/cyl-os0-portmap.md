# Cylinder OS0 (`MeasureHasGreenMomentBound`) — symmetric→asymmetric port map

*2026-05-26. The cylinder IR-limit OS0 input `MeasureHasGreenMomentBound`
(`AsymTorus/MomentBoundOS1.lean:107`) is a **port** of the already-proved symmetric
torus `T²_L` second-moment / propagator treatment — **not** the gibbs-variational
Boué–Dupuis route of `cyl-1a-bridge-plan.md`, which is redundant here. This doc lays
out the correspondence and isolates the single genuine delta.*

## Why BD is redundant, and what the real gap is

`MeasureHasGreenMomentBound μ` requires, for the UV-limit asym-torus interacting
measure `μ`:
```
∫ exp(|ω f|) dμ  ≤  K · exp(C · asymTorusContinuumGreen Lt Ls mass f f).
```
Already proved (no BD needed):
- the **cutoff exp-moment bound** `∫ exp|ωf| dμ_N ≤ K·exp(σ²_N(f))`, `K` *N-independent*
  (`asymTorusInteractingMeasure_exponentialMomentBound_cutoff`, via `asymNelson_exponential_estimate`);
- the **uniform second-moment bound** `σ²_N(f) ≤ C·‖f‖²_{seminorm}`
  (`asymGaussian_second_moment_uniform_bound`).

The only thing missing is the **Green form**: the RHS must be the *continuum torus
Green* `asymTorusContinuumGreen(f,f)`, not a seminorm — because that is what composes
with the cylinder method-of-images bound `torusGreen_uniform_bound` to give
`Lt`-uniformity (see `MomentBoundOS1.lean` docstring). The naive equality
`σ²_N = G` at finite `N` is **false** (cutoff-bound docstring warning); the correct
route is the **convergence** `σ²_N → G`, which the symmetric torus already proves.

## The symmetric template (all proved, `T²_L`)

| Object | Statement | Location |
|---|---|---|
| `lattice_second_moment_eq_inner` / `torusEmbeddedTwoPoint_eq_lattice_second_moment` | `σ²_N = ⟨G_N g, G_N g⟩` | `TorusPropagatorConvergence.lean:92,117` |
| `massEigenvalues_ge_mass_sq` + `covariance_inner_le_mass_inv_sq_norm_sq` | resolvent spectral bound `λ_k ≥ m²` ⟹ `⟨G_N·,·⟩ ≤ m⁻²‖·‖²` | `TPC:132,214` |
| `torusEmbeddedTwoPoint_le_seminorm_tight` / `torusEmbeddedTwoPoint_uniform_bound` | `σ²_N ≤ C·‖f‖²` (seminorm), uniform in `N` | `TPC:639,774` |
| **`torus_propagator_convergence`** | **`σ²_N(f,g) → torusContinuumGreen(f,g)`** (via gaussian-field `lattice_green_tendsto_continuum`; the GJ `(a^d)⁻¹`/`(L/N)` factors cancel in `d=2`) | **`TPC:547`** |
| Cauchy–Schwarz density transfer | interacting moment `≤ (Gaussian 4th moment)^{1/2}·√K` | `TorusInteractingLimit.lean` |
| `torus_interacting_tightness` | uniform 2nd moments ⟹ Mitoma tightness | `TorusInteractingLimit.lean:344` |

## The port to the asymmetric torus

| # | Symmetric (proved) | Asymmetric target | Status |
|---|---|---|---|
| 1 | `lattice_second_moment_eq_inner` | `second_moment_eq_covariance` | ✓ (used in #3) |
| 2 | `massEigenvalues_ge_mass_sq` + spectral bound | (in #3's proof) | ✓ |
| 3 | `torusEmbeddedTwoPoint_uniform_bound` (seminorm) | `asymGaussian_second_moment_uniform_bound` (`AsymTorusInteractingLimit.lean:331`) | ✓ DONE |
| 4 | **`torus_propagator_convergence`** (`σ²_N → G`) | **`asym_torus_propagator_convergence`** (`σ²_N → asymTorusContinuumGreen`) | **GAP — the one delta** |
| 5 | cutoff exp-moment (Nelson) | `asymTorusInteractingMeasure_exponentialMomentBound_cutoff` (`AsymTorusOS.lean:669`) | ✓ DONE |
| 6 | Cauchy–Schwarz density transfer | `asymTorus_interacting_second_moment_density_transfer` (`AsymTorusInteractingLimit.lean:415`) | ✓ DONE |
| 7 | `torus_interacting_tightness` | `asymTorus_interacting_tightness` (`:579`) | ✓ DONE |
| 8 | (limit exp-moment / weak-limit transfer) | `asymTorusInteracting_exponentialMomentBound` (`AsymTorusOS.lean:852`) | axiom on `main`; **theorem on PR #32** (`axiom-discharges-determinacy-expmoment`) |
| 9 | — (cylinder-specific) | `torusGreen_uniform_bound` (method of images, `Lt`-uniformity) | ✓ DONE (`gaussian-field/Cylinder/MethodOfImages.lean:349`) |
| 10 | — | **`MeasureHasGreenMomentBound`** (target) | assemble from #5 + #4 + #8 |

## The one delta: `asym_torus_propagator_convergence`

```
theorem asym_torus_propagator_convergence (mass : ℝ) (hmass : 0 < mass)
    (f g : AsymTorusTestFunction Lt Ls) :
    Tendsto (fun N : ℕ =>
        ∫ ω, (ω (asymLatticeTestFn Lt Ls (N+1) f)) * (ω (asymLatticeTestFn Lt Ls (N+1) g))
          ∂(latticeGaussianMeasure 2 (N+1) (asymGeomSpacing Lt Ls (N+1)) mass _ hmass))
      atTop (nhds (asymTorusContinuumGreen Lt Ls mass hmass f g))
```
**Port route** (mirror `torus_propagator_convergence`): the GJ-aligned asym embedding
(`asymLatticeTestFn` carries the `√(Lt·Ls)/N` geometric-mean factor via
`evalAsymAtFinSiteGJ`, `latticeCovarianceGJ` the `(a^d)⁻¹`) makes the same `d=2`
cancellation, reducing the pphi2-side wrapper to gaussian-field's bare-CLM convergence
on the asym `evalAsymAtFinSite` test functions.

### Where the delta actually bottoms out (traced 2026-05-26)

The pphi2 wrapper is a **clean mirror** of the symmetric proof — but it reduces to a
gaussian-field convergence that **does not yet exist**:

- gaussian-field's `lattice_green_tendsto_continuum` (`Lattice/Convergence.lean:1121`)
  and its per-mode core `lattice_green_tendsto_continuum_pure` (`:433`) are **square-only**:
  a single circle size `L` for both directions (`SmoothMap_Circle L`, square dispersion),
  target `greenFunctionBilinear`.
- The asym torus has the **same isotropic lattice covariance** (geometric-mean spacing
  `asymGeomSpacing`) but **rectangular evaluation** — `evalAsymTorusAtSite` uses `Lt/N`
  (time) and `Ls/N` (space) per direction — converging to the **rectangular**
  `asymTorusContinuumGreen` (dispersion `(2πp/Lt)² + (2πq/Ls)² + m²`).

So the genuine missing piece is a **rectangular generalization of
`lattice_green_tendsto_continuum`** in gaussian-field: the lattice→continuum Green
convergence with `SmoothMap_Circle Lt ⊗ SmoothMap_Circle Ls` test functions and the
rectangular continuum Green. The *core convergence* (isotropic lattice resolvent →
continuum resolvent) is shared with the square case; only the test-function space and
the continuum target change.

**Cost.** The proof is assembled **per Fourier mode** (Tannery over `ℕ×ℕ` +
`latticeDFTCoeff1d_quadratic_bound` per 1D direction). If the 2D term `latticeGreenTerm2d`
factors into 1D terms parametric in the circle size, the rectangular version is a
**moderate refactor** (instantiate the two factors with `Lt`, `Ls`); otherwise a larger
re-derivation. This is standard constructive-QFT analysis (Glimm–Jaffe), not novel math.

**Decision (effort vs. axiom).** Two options:
- **(a) Generalize the gaussian-field proof** to the rectangle — zero-axiom, real labor
  (size set by the 1D factorization; check `latticeGreenTerm2d` first).
- **(b) Vetted textbook axiom.** The lattice→continuum covariance convergence on a
  rectangular torus is a standard, well-established fact, and the *square* case is fully
  proved (`torus_propagator_convergence`) — strong evidence it is formalizable. Per the
  project's textbook-axiom policy, state `asym_torus_propagator_convergence` as a cited,
  audited axiom (Glimm–Jaffe; symmetric analogue proved) and spend effort on the harder,
  more novel pieces (OS3 RP, or the OS4 mass gap). The pphi2 wrapper + assembly close the
  cylinder OS0 chain either way.

## Assembly of `MeasureHasGreenMomentBound`

From #5 (cutoff): `∫ exp|ωf| dμ_N ≤ K·exp(σ²_N(f))`, `K` uniform.
From #4 (convergence): `σ²_N(f) → asymTorusContinuumGreen(f,f)`.
From #8 (PR #32 limit transfer / lower-semicontinuity under `μ_N ⇀ μ`):
```
∫ exp|ωf| dμ  ≤  liminf_N K·exp(σ²_N(f))  =  K·exp(asymTorusContinuumGreen(f,f)),
```
i.e. `MeasureHasGreenMomentBound` with `C = 1`. Then
`AsymTorusSequenceHasUniformGreenMomentBound.of_forall_ge_one` (`IRTightness.lean:68`)
packages the uniform-in-`Lt` family, and `routeBPrime_cylinder_OS` (`CylinderOS.lean:460`)
consumes it for cylinder OS0 (the cylinder `Lt`-uniformity uses #9).

## Order of work

1. **Port #4** — prove `asym_torus_propagator_convergence` (the delta; reuse
   `lattice_green_tendsto_continuum` + asym embedding cancellation).
2. **Merge PR #32** — makes #8 (`asymTorusInteracting_exponentialMomentBound`) a
   theorem on `main` (the limit-transfer base; also clears the on-`main` axiom).
3. **Assemble** `MeasureHasGreenMomentBound` (#5 + #4 + #8), then
   `AsymTorusSequenceHasUniformGreenMomentBound`, then feed `routeBPrime_cylinder_OS`.

Net: **one convergence lemma + the PR #32 merge + a short assembly** — a port of the
symmetric treatment, not new analysis and not the BD stack. (Supersedes the BD route
in `cyl-1a-bridge-plan.md`.)
