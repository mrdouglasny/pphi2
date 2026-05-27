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

> **Status (2026-05-26). Phases 1a + 1b COMPLETE.** `gaussian-field/Lattice/AsymCovariance.lean`
> builds with **0 sorry, 0 custom axioms** (`lattice_green_tendsto_continuum_asym` depends only
> on `[propext, Classical.choice, Quot.sound]`); full `lake build` green. The rectangular
> lattice→continuum Green's-function convergence — the honest, metric-correct cylinder-OS0
> "delta" (dispersion `(2πp/Lt)²+(2πq/Ls)²`, `Lt`-uniform) — is a proved theorem, on branch
> `cylinder-isotropic-lattice`. Commits `ab7b3ed`→`5bb35e8`.
> Key discovery: `latticeCovariance := spectralLatticeCovariance` *definitionally*
> (`Covariance.lean:97`), so `spectralLatticeCovarianceAsym` is exactly the right object and
> the square convergence machinery ports directly.
>
> **Remaining for the cylinder construction:** Phase 2 (pphi2 `AsymTorus/` refactor —
> replace `finToAsymSite`/`asymGeomSpacing` with the `Z_Nt×Z_Ns` isotropic lattice and
> re-target the embedding/cutoff/Nelson/second-moment to it) and Phase 3 (assemble
> `MeasureHasGreenMomentBound` as a theorem from the cutoff bound + this convergence + the
> limit transfer, feeding `routeBPrime_cylinder_OS`). These are in pphi2, not gaussian-field.
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
> 5. **The convergence** `lattice_green_tendsto_continuum_asym` — IN PROGRESS. Sub-blocks:
>    - ✅ **DONE** (`01ed8d4`) — domination block: `latticeGreenTerm2dAsym`,
>      `continuumGreenTerm2dAsym`, `latticeGreenTerm2dAsym_zero_of_ge`,
>      `latticeGreenTerm2dAsym_norm_le` (per-direction DFT quadratic decay; per-size bound
>      hyps), `summable_bound_asym`. (Term def needs `[NeZero Nt] [NeZero Ns]` since it uses
>      `Nt/Ns` directly, unlike the square's `N+1`.)
>    - ✅ **DONE** (`9949a19`) — per-mode convergence `latticeGreenTerm2dAsym_tendsto`, via
>      the `Nt k − 1` reindexing of the square `N+1`-form 1D inputs (`tendsto_inv_nhdsGT_zero`
>      for `Nt k → ∞`, `.comp hNt1` + `Tendsto.congr` with `(Nt k−1)+1 = Nt k`, then
>      `Tendsto.div` of the 4-DFT numerator by the `(eig+eig+mass²)·normSq·normSq` denominator).
>      The instance-in-`k`-lambda (`[NeZero (Nt k)]`) assembled through defeq without issue.
>    - ✅ **DONE** (`e675ead`) — covariance↔tsum (`lattice_covariance_pure_eq_2d_spectral_asym`
>      + `lattice_covariance_eq_tsum_pure_asym`): the bridge + `hpure`
>      (`evalAsym (pure) = circleRestriction ⊗ circleRestriction`) + `hcoeff`
>      (`sum_factor_asym` + `Fintype.sum_mul_sum`, `dsimp only` to reduce `(a,b).1/.2`) +
>      `tsum_eq_sum`.
>    - ✅ **DONE** (`ebc54b5`) — continuum↔tsum (`greenFunctionBilinear_pure_eq_tsum_asym`):
>      NTP eigenvalue = sum of 1D eigenvalues (rfl), `NuclearTensorProduct.pure_val`,
>      `Nat.pairEquiv.symm.tsum_eq`. (Needed to qualify `NuclearTensorProduct.pure_val` —
>      this file does not `open NuclearTensorProduct`.)
>    - ✅ **DONE** (`d21b421`) — Tannery assembly for pure tensors
>      (`lattice_green_tendsto_continuum_asym_pure`): `tendsto_tsum_of_dominated_convergence`
>      over per-mode + domination + summability; per-size DFT bounds from the uniform
>      quadratic bound via `(Nt k − 1)+1 = Nt k`.
>    - **DM-expansion to general elements** (`lattice_green_tendsto_continuum_asym`) — IN PROGRESS:
>      - ✅ **DONE** (`a15c602`) — infrastructure: `ntp_basis_eq_pure_asym`,
>        `greenFunctionBilinear_continuous_left_asym` + `greenCLM_left_asym`, `evalLatticeMapAsym`,
>        `latticeCovCLM_left_asym`, `covariance_dm_expansion_left_asym`, `summable_inv_sq_sq_asym`.
>        (All names resolved first try.)
>      - ✅ **DONE** (`6481d5b`) — `lattice_covariance_pure_abs_le_asym` (mixed flat×quadratic
>        uniform bound; per-size hyps; keep the `0 ≤ C` from `quadratic_bound`, don't `by positivity`).
>      - ✅ **DONE** (`d0ce67f`) — `latticeDFTCoeff1d_seminorm_quadratic_gen` (re-port of the
>        private square seminorm-explicit quadratic bound, for a general circle size).
>      - ✅ **DONE** (`9e29ffb`) — `lattice_green_tendsto_pure_right_asym` (Phase A: general `f`,
>        pure `g`), two-factor adaptation with distinct `basis_growth` exponents `r₁, r₂`.
>      - ✅ **DONE** (`5bb35e8`) — `lattice_covariance_general_basis_bound_asym` (four
>        `basis_growth` invocations, sobolev 0/2 × `SMC Lt`/`SMC Ls`; `rn = r₀₁+r₀₂`, `rm = rq₁+rq₂`)
>        **and the main theorem** `lattice_green_tendsto_continuum_asym` (Phase-B DM-expansion in `g`).
>        Per-size flat/quad bounds via `simp only [(Nt k−1)+1 = Nt k]` (not `rw` — dodges the
>        `[NeZero]` instance-motive issue).
>      **Phase 1b COMPLETE: 0 sorry, 0 custom axioms, full `lake build` green.**
>    The 1D domination `latticeDFTCoeff1d_quadratic_bound L` reused verbatim per direction
>    (any size = `N+1`), so `Lt≠Ls` obstruction gone, constants `Lt`-uniform.
>    - **Continuum target:** scaffold states `greenFunctionBilinear mass hmass f g` on
>      `AsymTorusTestFunction Lt Ls = SMC Lt ⊗̂ SMC Ls`; its eigenvalues come from
>      `HasLaplacianEigenvalues (SMC Lt)`/`(SMC Ls)` = `(2πp/Lt)²`/`(2πq/Ls)²` — i.e. the
>      correct rectangular Green, so no realignment needed (matches `continuumGreenTerm2dAsym`).

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

> **Status (2026-05-27). Phase 2 COMPLETE** — measure + embedding + second moment + Nelson
> estimate + cutoff exp-moment bound, all building clean, wired into `Pphi2.lean`. New since the
> 05-26 foundation:
> - `Pphi2/GeneralResults/GaussianExpMoment.lean`: `GaussianField.gaussian_exp_abs_moment` —
>   **generic** (covariance-agnostic) Gaussian exp-modulus MGF bound `∫ exp(t|ωg|) d(measure T) ≤
>   2 exp(t²/2·∫(ωg)²)`, 0 axioms. Instantiates at any lattice covariance.
> - `Pphi2/AsymTorus/AsymWickMean.lean`: the vetted axiom `wickConstantAsym_eq_variance` (site
>   variance = Wick constant; circulant translation invariance), then the proved chain
>   `wickMonomialAsym_latticeGaussian` → `wickPolynomialAsym_integral_eq_coeff_zero` →
>   `interactionFunctionalAsym_mean_nonpos` → `partitionFunctionAsym_ge_one` (`Z_a ≥ 1`), and
>   `density_transfer_bound_iso` (Cauchy–Schwarz density transfer).
> - `Pphi2/AsymTorus/AsymNelson.lean`: the vetted axiom `asymChaosCutoffDecomposition` + the
>   proved heterogeneous Nelson estimate `asymNelson_exponential_estimate_iso` (B-lean engine).
> - `Pphi2/AsymTorus/AsymCutoffBound.lean`:
>   `asymTorusInteractingMeasureIso_exponentialMomentBound_cutoff` — `∫ exp|ωf| dμ̃_int ≤
>   K·exp(σ²)` with `K` the uniform Nelson constant and `σ²` the heterogeneous lattice second
>   moment. Depends only on `[propext, Classical.choice, Quot.sound, asymChaosCutoffDecomposition,
>   wickConstantAsym_eq_variance]`.
>
> **Remaining: Phase 3** — assemble `MeasureHasGreenMomentBound` from this cutoff bound + the
> Phase-1+2 second-moment→continuum-Green convergence (`second_moment_asym_tendsto`) + the
> weak-limit transfer, feeding `AsymTorusSequenceHasUniformGreenMomentBound.of_forall_ge_one` →
> `routeBPrime_cylinder_OS`.
>
> **Earlier status (2026-05-26).** The measure-theoretic + embedding **foundation** on pphi2
> branch `cylinder-isotropic-lattice` (gaussian-field pinned at `5bb35e8`, commit `13a600e`).
> Two new files, all building clean:
> - `Pphi2/AsymTorus/AsymLatticeMeasure.lean` (`f8de94c`, `6403b47`): `DyninMityaginSpace
>   (AsymLatticeField Nt Ns)` instance (port of the square, Fintype-generic),
>   `latticeGaussianMeasureAsym` (+`IsProbabilityMeasure`), and the full heterogeneous interacting
>   measure — `wickConstantAsym` (`(a²)⁻¹·(1/(Nt·Ns))·Σ_k 1/λ_k` via `massEigenvaluesAsym`),
>   `interactionFunctionalAsym` (+`_measurable`, +`_bounded_below`), `boltzmannWeightAsym`
>   (+`_pos`, +`_integrable`), `partitionFunctionAsym` (+`_pos`), `interactingLatticeMeasureAsym`
>   (+`_isProbability`).
> - `Pphi2/AsymTorus/AsymTorusEmbeddingIso.lean` (`acb0393`): `evalAsymTorusAtSiteGJ` (GJ weight
>   = `a`), `asymTorusEmbedLiftIso` (+`_measurable`), `asymLatticeTestFnIso` (+`_expand`),
>   `asymTorusEmbedLiftIso_eval_eq`, `asymTorusInteractingMeasureIso` (pushforward).
>
> **Key normalisation (worked out):** the GJ weight `a` and the `(1/a)²` of `latticeCovarianceAsymGJ`
> cancel, so the embedded second moment is `covariance (spectralLatticeCovarianceAsym)
> (evalAsym f) (evalAsym g)` — *exactly* the form `lattice_green_tendsto_continuum_asym` converges
> to `greenFunctionBilinear`. So `second_moment_eq_covariance` + the convergence is a short bridge.
>
> **Remaining (the analytic estimates, porting from `AsymTorusOS.lean`):** the **Nelson cutoff
> exp-moment bound** on the iso lattice (largest piece), `second_moment_eq_covariance`
> (σ² = covariance of the embedded Gaussian → the spectral form above), and the **uniform
> second-moment** bounded by `asymTorusContinuumGreen` via Phase 1b. Then Phase 3.

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

> **Status (2026-05-27). Phase 3 COMPLETE** (conditional on the one volume-uniformity input,
> 0 new axioms), in `AsymTorus/AsymContinuumLimit.lean` + `GeneralResults/WeakLimitMoment.lean`:
> - `asymTorusIso_interacting_second_moment_density_transfer` / `_uniform`: interacting 2nd moment
>   ≤ `3√K`·(free Gaussian 2nd moment), uniformly bounded along an isotropic sequence (the free 2nd
>   moment *converges* to the Green's function, hence is bounded).
> - `asymTorusIso_interacting_limit_exists`: tightness (`configuration_tight_of_uniform_second_
>   moments`) + Prokhorov → the UV continuum limit `μ` on the fixed-`(Lt,Ls)` torus.
> - `GaussianField.weakLimit_exponential_moment` (generic): the truncation+MCT transfer of an
>   exp-moment bound `∫ exp|ωf| dνₙ ≤ Bₙ → B∞` through a bounded-continuous weak limit.
> - `asymTorusIso_measureHasGreenMomentBound`: **`MeasureHasGreenMomentBound` is a theorem** for the
>   UV limit (`C = 1`) — the crux the metric-mismatched square construction never produced.
> - `asymTorusIso_cylinderUniformGreenBound`: from a *single* volume-uniform Nelson constant `Knel`
>   it builds the full IR family (`Lt n = (n+1)·Ls → ∞`, rational-compatible; exactly-isotropic
>   sequence `Ns_k = k+1`, `a_k = Ls/(k+1)`, `Nt_k = (n+1)(k+1)`) and proves
>   `AsymTorusSequenceHasUniformGreenMomentBound` with the single constant `√(2 Knel)`.
> - `routeBPrimeIso_cylinder_OS`: feeds `routeBPrime_cylinder_OS` to yield cylinder OS0/OS1/OS2/OS3,
>   conditional on (i) the volume-uniform Nelson bound `Knel`, (ii) OS3 reflection positivity,
>   (iii) OS2 symmetry — the three separate inputs.
>
> **The volume-uniformity** (a single `Knel` across all periods `Lt`) is the genuine remaining
> analytic content (cluster-expansion-level, per `MomentBoundOS1.lean`'s docstring); it is taken as
> an explicit hypothesis rather than axiomatized, so the assembly is **axiom-free** (depends only on
> the two existing isotropic axioms + the standard trio; the cylinder-OS theorem also pulls the
> pre-existing `GaussianField.embed_l2_uniform_bound` via `routeBPrime`).

```
∫ exp|ωf| dμ_{Nt,Ns} ≤ K·exp(σ²_{Nt,Ns}(f))     [Phase 2 cutoff bound, K uniform at fixed volume]
σ²_{Nt,Ns}(f) → asymTorusContinuumGreen(f,f)      [Phase 1b convergence, TRUE]
μ_{Nt,Ns} ⇀ μ  ⟹  ∫ exp|ωf| dμ ≤ K·exp(asymTorusContinuumGreen(f,f))   [truncation + MCT]
```
⟹ `MeasureHasGreenMomentBound` (`C=1`) as a **theorem**. Then a single volume-uniform `Knel`
gives `AsymTorusSequenceHasUniformGreenMomentBound`, and `routeBPrime_cylinder_OS`
(`CylinderOS.lean:460`) gives cylinder OS0+OS1+OS2(+OS3 with the RP input). (OS4 is the separate
cyl-2 mass gap.)

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
