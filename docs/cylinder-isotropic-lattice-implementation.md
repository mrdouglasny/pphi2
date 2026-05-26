# Isotropic `Z_{Nt}×Z_{Ns}` cylinder lattice — implementation plan

*2026-05-26. The detailed, phase-by-phase build plan for the manifestly-correct cylinder construction of
`cylinder-isotropic-lattice-redesign.md`: a single isotropic spacing `a` on `AsymLatticeSites Nt Ns =
ZMod Nt × ZMod Ns` with `a = Lt/Nt = Ls/Ns`. Replaces the metric-inconsistent `N×N` + geometric-mean
construction. Key enabler (verified): gaussian-field's convergence is assembled from **per-direction
1D pieces** that already take their own circle size and site count, so the rectangle is a re-assembly,
not a re-derivation.*

## Phase 0 — parametrization (and why the cylinder avoids the rationality snag)

Single spacing `a`; site counts `Nt`, `Ns`; periods `Lt = Nt·a`, `Ls = Ns·a`. Cell area `a²`, volume
`Nt·Ns·a² = Lt·Ls`. Two regimes:

- **Rectangular torus (fixed `Lt, Ls`):** need `a = Lt/Nt = Ls/Ns`, i.e. `Nt/Ns = Lt/Ls`. For `Lt/Ls =
  p/q` rational, the sequence `Nt = k·p`, `Ns = k·q`, `a = Lt/(kp) → 0` is **exactly isotropic** at every
  `k`. (Irrational `Lt/Ls`: approximate; messier — avoid by working with the cylinder directly.)
- **Cylinder `S¹(Ls)×ℝ` (the goal) — no rationality snag:** fix `a = Ls/Ns` (spatial spacing exact),
  let `Nt → ∞` so `Lt = Nt·a → ∞` (time decompactifies to `ℝ`), *then* `Ns → ∞` (`a → 0`, UV). The
  spatial spacing is always exact; `Lt` is a free IR cutoff. This is the natural transfer-matrix picture
  (spatial circle `Z_{Ns}`, time `ℤ`).

## Phase 1 — gaussian-field: heterogeneous covariance + convergence

> **Status (2026-05-26).** Phase 1a is **DONE** and committed on branch
> `cylinder-isotropic-lattice` (`gaussian-field/Lattice/AsymCovariance.lean`); Phase 1b's
> DFT-side foundation is done too. Commits: `ab7b3ed` (chain), `21f306c`
> (`finiteLaplacianAsym_selfAdjoint`), `ee953fd` (rectangular Parseval + product eigenvector).
> The single remaining `sorry` is `lattice_green_tendsto_continuum_asym` (the convergence).
> Key discovery: `latticeCovariance := spectralLatticeCovariance` *definitionally*
> (`Covariance.lean:97`), so `spectralLatticeCovarianceAsym` is exactly the right object —
> no `latticeCovarianceAsym` synonym needed, and the square convergence machinery (stated
> over `latticeCovariance`) applies once the bridge below is in place.
>
> **Phase 1b port checklist** (dependency order; the convergence sorry sits on top):
> 1. ✅ **DONE** (`ee953fd`, `161b2dc`, `bec5bcb`) — **abstract-spectral side**:
>    `asym_field_basis_decomp`, `asym_direction_sum_eq_neg_sq`,
>    `finiteLaplacianAsym_neg_semidefinite`, `massOperatorAsym_pos_def`,
>    `massOperatorAsym_eq_matrix_mulVec`, `massOperatorAsym_eigenCoeff_eq_eigenvalues_mul_eigenCoeff`,
>    `massEigenbasisAsym_sum_mul_sum_eq_site_inner`, `massOperatorMatrixAsym_eigenvalues_pos`,
>    `spectralLatticeCovarianceAsym_inner`, plus DFT-side `sum_factor_asym`,
>    `dft_parseval_2d_asym`, `massOperator_product_eigenvector_asym`. (Needed
>    `import Mathlib.Analysis.Matrix.PosDef`; use `.mulVec` method, not `*ᵥ`.)
> 2. ✅ **DONE** (`8492cc9`) — `massOperatorAsym_surjective`.
> 3. ✅ **DONE** (`8492cc9`) — `dft_eigencoeff_massOperatorAsym`.
> 4. ✅ **DONE** (`8492cc9`) — `abstract_spectral_eq_dft_spectral_2d_asym` (the bridge, +
>    helper `covariance_spectralLatticeCovarianceAsym_eq`). **All new rectangular spectral
>    infrastructure proved; the convergence is now "just" Tannery.**
> 5. **TODO — the convergence** `lattice_green_tendsto_continuum_asym`. Port the
>    `Convergence.lean` Tannery stack (`latticeGreenTerm2dAsym`, `_tendsto`, `_norm_le`,
>    `summable_bound`, `_pure`, then DM-expansion to general elements). Connection: identify
>    `covariance (spectralLatticeCovarianceAsym …) (evalAsym (pure f₁ f₂)) (evalAsym (pure g₁ g₂))`
>    with `∑ latticeGreenTerm2dAsym` via `abstract_spectral_eq_dft_spectral_2d_asym` (step 4)
>    + `evalAsymTorusAtSite` on pure tensors = product of `circleRestriction`s (mirror
>    `lattice_covariance_pure_eq_2d_spectral`, `Convergence.lean:67`). The 1D domination
>    `latticeDFTCoeff1d_quadratic_bound L` is reused **verbatim per direction** (`Lt`, `Ls`),
>    so the `Lt≠Ls` obstruction is gone and constants are `Lt`-uniform. Largest sub-piece (~the
>    bulk of the 1219-line `Convergence.lean`, re-assembled with two circle sizes sharing `a`).
>    Check the continuum target: scaffold currently states `greenFunctionBilinear mass hmass f g`
>    — confirm this is the rectangular-torus Green (dispersion `(2πp/Lt)²+(2πq/Ls)²`) vs.
>    `asymTorusContinuumGreen`, and align if needed.

### 1a. Isotropic covariance on `AsymLatticeField Nt Ns`

Generalize `spectralLatticeCovariance d N` (`Lattice/Covariance.lean:94`, on square `FinLatticeField d N`)
to the heterogeneous lattice:
```
spectralLatticeCovarianceAsym (Nt Ns : ℕ) (a mass : ℝ) (ha hmass) :
    AsymLatticeField Nt Ns →L[ℝ] ell2'
```
isotropic resolvent `(−Δ_a + m²)⁻¹` on `ZMod Nt × ZMod Ns`, single spacing `a`. Spectral form: eigenvalues
`latticeEigenvalue1d Nt a p + latticeEigenvalue1d Ns a q` (**1D circulant DFTs of sizes `Nt`, `Ns`** —
already parametric). Then, mirroring the square defs:
```
latticeCovarianceAsymGJ Nt Ns a mass = (a²)^{−1/2} • spectralLatticeCovarianceAsym …   (d=2 factor)
latticeGaussianMeasureAsym Nt Ns a mass = GaussianField.measure (latticeCovarianceAsymGJ …)
```
**Reuse:** the 1D DFT eigenvalue/Parseval machinery (`CirculantDFT2d.lean`: `dft_1d_eigenvalue_pointwise`,
`dft_parseval_1d` on `ZMod N`, `massOperator_product_eigenvector`). **New:** the 2D Parseval
`dft_parseval_2d` is square (`FinLatticeSites 2 N`) — generalize to `ZMod Nt × ZMod Ns` as the product of
two 1D Parsevals of sizes `Nt`, `Ns` (a clean tensor of the existing 1D result).

### 1b. The convergence (now TRUE — the honest cyl-os0 delta)

Re-assemble the 2D Green term with two directions sharing `a`:
```
latticeGreenTerm2dAsym Nt Ns a mass (f₁ g₁ : SMC Lt) (f₂ g₂ : SMC Ls) (p : ℕ×ℕ) :=
  latticeDFTCoeff1d Lt Nt f₁ p.1 · latticeDFTCoeff1d Lt Nt g₁ p.1 ·
  latticeDFTCoeff1d Ls Ns f₂ p.2 · latticeDFTCoeff1d Ls Ns g₂ p.2 /
  ((latticeEigenvalue1d Nt a p.1 + latticeEigenvalue1d Ns a p.2 + mass²) ·
   latticeFourierNormSq Nt p.1 · latticeFourierNormSq Ns p.2)
```
(cf. the square `latticeGreenTerm2d`, `Convergence.lean:141`, which uses one `(L,N)` for both legs).
Then:
```
lattice_green_tendsto_continuum_asym (mass) (hmass) (f g : AsymTorusTestFunction Lt Ls) :
  Tendsto (fun k => covariance (latticeCovarianceAsym Nt_k Ns_k a_k mass …) (evalAsym … f) (evalAsym … g))
    atTop (nhds (asymTorusContinuumGreen Lt Ls mass hmass f g))
```
**Proof = port of `lattice_green_tendsto_continuum(_pure)`:** Tannery over `ℕ×ℕ` with
- **per-mode convergence:** `latticeEigenvalue1d Nt_k a_k p → (2πp/Lt)²` (direction-1, `Nt_k·a_k=Lt`) and
  `latticeEigenvalue1d Ns_k a_k q → (2πq/Ls)²` (direction-2) — the 1-cos Taylor, per direction;
- **domination:** `latticeDFTCoeff1d_quadratic_bound Lt f₁`, `… Ls f₂` (per-direction, already parametric)
  → the summable bound `C/(m²(1+p)⁴(1+q)⁴)`;
then DM-expand `f,g` in the `SMC Lt ⊗ SMC Ls` basis to reduce to pure tensors. **The `Lt≠Ls`
obstruction is gone** (the eigenvalues are now the correct rectangular ones), and the constants are
**uniform in `Lt`** (1D bounds depend on `Lt`, `Ls` separately, not on `√(Lt·Ls)`).

## Phase 2 — pphi2 `AsymTorus/` refactor

Replace the `N×N` + `asymGeomSpacing` layer:

| Remove (current) | Add (isotropic) |
|---|---|
| `finToAsymSite : FinLatticeSites 2 N → AsymLatticeSites N N` | direct use of `AsymLatticeSites Nt Ns` |
| `asymGeomSpacing = √(Lt·Ls)/N` | spacing `a` with `Nt = Lt/a`, `Ns = Ls/a` |
| `evalAsymAtFinSite(GJ)` (via `finToAsymSite`) | `evalAsymTorusAtSite Nt Ns` directly (isotropic at `a=Lt/Nt=Ls/Ns`), GJ weight `a` |
| `asymTorusEmbedLift` (N×N) | `asymTorusEmbedLiftIso Nt Ns a` on `Configuration (AsymLatticeField Nt Ns)` |
| `asymLatticeTestFn` (N×N) | `asymLatticeTestFnIso Nt Ns a` |

Then re-derive on the new lattice (each is a port of its current form with `Nt,Ns,a` for `N,a_geom`):
- `asymTorusEmbedLiftIso_eval_eq` (embedding eval identity),
- `second_moment_eq_covariance` (σ² = covariance of `latticeCovarianceAsymGJ`),
- **cutoff exp-moment bound** `∫ exp|ωf| dμ_{Nt,Ns} ≤ K·exp(σ²_{Nt,Ns}(f))` — Nelson estimate on the
  isotropic lattice (cell area `a²`, volume `Lt·Ls`; cleaner than `a_geom`),
- **uniform second-moment** — but now bound by `asymTorusContinuumGreen` directly via Phase 1b
  (replacing the seminorm bound `asymGaussian_second_moment_uniform_bound`).

`IRLimit/` is abstract (0-axiom) and just re-targets to the new lattice family.

## Phase 3 — assembly (`MeasureHasGreenMomentBound` becomes a theorem)

```
∫ exp|ωf| dμ_{Nt,Ns} ≤ K·exp(σ²_{Nt,Ns}(f))     [Phase 2 cutoff bound, K uniform]
σ²_{Nt,Ns}(f) → asymTorusContinuumGreen(f,f)      [Phase 1b convergence, TRUE]
μ_{Nt,Ns} ⇀ μ  ⟹  ∫ exp|ωf| dμ ≤ K·exp(asymTorusContinuumGreen(f,f))   [lower-semicontinuity]
```
⟹ `MeasureHasGreenMomentBound` (`C=1`) as a **theorem, no axiom**. Then
`AsymTorusSequenceHasUniformGreenMomentBound.of_forall_ge_one` (`IRTightness.lean:68`) — *uniform in `Lt`*
because Phase 1b's constants are — and `routeBPrime_cylinder_OS` (`CylinderOS.lean:460`) gives cylinder
OS0+OS1+OS2. (OS3 is the separate eventual-RP input; OS4 the separate cyl-2 mass gap.)

## Correspondence (square proved → heterogeneous target)

| square (proved) | heterogeneous target | reuse / new |
|---|---|---|
| `spectralLatticeCovariance d N` | `spectralLatticeCovarianceAsym Nt Ns` | new (from 1D DFT pieces) |
| `dft_parseval_2d` (square) | 2D Parseval on `ZMod Nt × ZMod Ns` | new (tensor of 1D Parseval) |
| `latticeDFTCoeff1d L N`, `latticeEigenvalue1d N a` | same, per direction `(Lt,Nt)`/`(Ls,Ns)` | **reuse verbatim** |
| `latticeGreenTerm2d` | `latticeGreenTerm2dAsym` | re-assembly (2 dirs, shared `a`) |
| `lattice_green_tendsto_continuum(_pure)` | `lattice_green_tendsto_continuum_asym` | port (Tannery + 1D pieces) |
| `torus_propagator_convergence` | `asym_torus_propagator_convergence` | port (pphi2 wrapper) |
| cutoff bound / Nelson / 2nd moment (sym) | asym isotropic versions | port (Nt,Ns,a for N,a_geom) |

## Technical subtleties to get right

1. **GJ normalization:** `d=2` factor `(a²)^{−1/2} = 1/a`, identical to the symmetric `d=2`; the cell
   area is `a²` (isotropic), volume `Lt·Ls` — the Nelson cell-area input is now exact and natural.
2. **2D Parseval on `ZMod Nt × ZMod Ns`:** the one genuinely new gaussian-field lemma; everything else
   reuses 1D. Build it as `dft_parseval_1d (Nt) ⊗ dft_parseval_1d (Ns)`.
3. **Sequence indexing:** for the cylinder, parametrize by `(Ns, Nt)` with `a = Ls/Ns`, `Lt = Nt·a`; the
   `Tendsto` is over the UV index (`Ns→∞`, `a→0`) at fixed `Lt`, with a separate `Nt→∞` (IR) — keep the
   two limits' indices explicit (`IRLimit/` already separates them).
4. **Don't reintroduce the metric mismatch:** the spacing fed to the covariance MUST equal the
   evaluation spacing (`a = Lt/Nt = Ls/Ns`). Add a guarding hypothesis `Nt·Ls = Ns·Lt` (or define `a`
   once and derive `Nt, Ns`) so the two can't drift apart again.

## Effort (rough)

- Phase 1a (heterogeneous covariance + 2D Parseval): moderate — new construction, 1D ingredients exist.
- Phase 1b (convergence port): moderate — re-assembly + Tannery, 1D pieces reused.
- Phase 2 (pphi2 refactor): moderate-large — touches the `AsymTorus/` stack, but each piece is a port.
- Phase 3 (assembly): small.

The payoff: a manifestly-correct cylinder construction in which `MeasureHasGreenMomentBound` is a
**proved theorem** (no axiom, no metric mismatch, `Lt`-uniform), closing cylinder OS0–OS2 on a sound base.
