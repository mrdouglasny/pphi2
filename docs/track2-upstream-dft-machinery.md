# Track 2: Move generic d-dim DFT machinery to gaussian-field

## Goal

Move the d-dim lattice DFT material currently in pphi2's `GeneralResults/`
into gaussian-field, where it morally belongs (it's about gaussian-field's
own primitives: `latticeFourierBasisFun`, `latticeEigenvalue1d`,
`massOperator`, `latticeCovariance`).

After this move, the d=2-only specializations in
gaussian-field's `Lattice/CirculantDFT2d.lean` either become trivial
corollaries or can be deleted outright.

## What moves

**From `Pphi2/GeneralResults/LatticeProductDFT.lean`** (~570 lines, all proved):
- `latticeFourierProductBasisFun N d m` — d-dim product basis
- `latticeFourierProductNormSq N d m` — Nyquist-aware norm²
- `latticeFourierProductCoeff N d f m`
- `latticeFourierProductBasis_sq_sum`
- `latticeFourierProductNormSq_pos`
- `latticeFourierProductCoeff_succ`, `sum_finLatticeSites_succ`
- `dft_parseval_family`
- `massOperator_surjective`
- `massOperator_product_eigenvector_family`
- `dft_eigencoeff_massOperator_family`
- `abstract_spectral_eq_dft_spectral_family`

**From `Pphi2/GeneralResults/LatticeFourierIndexing.lean`** (~340 lines):
- `realModeRawEquivFamily`
- `sum_latticeEigenvalue_eq_sum_latticeEigenvalue1d_family`
- `sum_rawFrequency_eq_sum_latticeEigenvalue1d`
- `sum_latticeEigenvalue_two_eq_sum_latticeEigenvalue1d_pair`
- `sum_rawFrequency_pair_eq_sum_latticeEigenvalue1d_pair`
- supporting helpers (mode index bridges)

Total: **~15 declarations** plus helpers (~900 lines of code).

## Where they go

New file `gaussian-field/Lattice/CirculantDFTFamily.lean` (or a couple of
files if natural; e.g. `LatticeFourierProduct.lean` + `LatticeFourierIndexing.lean`).

Subsumes:
- `gaussian-field/Lattice/CirculantDFT2d.lean` d=2 versions:
  `dft_parseval_2d`, `massOperator_product_eigenvector` (d=2),
  `abstract_spectral_eq_dft_spectral_2d`, `dft_eigencoeff_massOperator_2d`.
  Either delete them or keep as one-line corollaries (`exact … d := 2`).

## Phases

### Phase 0 — Local-path setup (~30min)
- Branch on `~/Documents/GitHub/gaussian-field`: `feature/dft-product-family`.
- Switch `pphi2/lakefile.toml` require to `path = "../gaussian-field"`.

### Phase 1 — Create new file(s) in gaussian-field (~1.5 days)
- Add `Lattice/LatticeFourierProduct.lean` containing the product-basis
  machinery (basis fun, norm², coeff, Parseval).
- Add `Lattice/LatticeFourierIndexing.lean` containing the mode-index
  bijections (`realModeRawEquivFamily` etc.).
- Update gaussian-field's lakefile/module exports.
- Verify they compile in gaussian-field standalone.

### Phase 2 — Move/copy the proofs (~1 day)
- Copy each declaration from pphi2 into the new gaussian-field files.
- Adjust imports (the gaussian-field side won't have access to pphi2
  paths, so refactor any pphi2-internal references).
- Verify gaussian-field builds clean.

### Phase 3 — Update pphi2 imports (~0.5 days)
- Replace `import Pphi2.GeneralResults.LatticeProductDFT` with
  `import GaussianField.Lattice.LatticeFourierProduct` (etc.) wherever
  used.
- Files affected: `Pphi2/ContinuumLimit/Hypercontractivity.lean`,
  `Pphi2/TorusContinuumLimit/TorusPropagatorConvergence.lean`,
  `Pphi2/GaussianContinuumLimit/{Propagator,Embedded}Covariance.lean`,
  `Pphi2/NelsonEstimate/FieldDecomposition.lean`, possibly others.
- Delete `Pphi2/GeneralResults/LatticeProductDFT.lean` and
  `Pphi2/GeneralResults/LatticeFourierIndexing.lean`.

### Phase 4 — Subsume d=2 specializations (~0.5 days)
- In gaussian-field's `Lattice/CirculantDFT2d.lean`, replace
  `dft_parseval_2d`, `massOperator_product_eigenvector`,
  `abstract_spectral_eq_dft_spectral_2d`, `dft_eigencoeff_massOperator_2d`
  with one-line corollaries of the family versions, OR delete them and
  update consumers (mostly internal to gaussian-field).

### Phase 5 — Final pin update (~30min)
- Push gaussian-field branch.
- Update `pphi2/lakefile.toml` rev to the new commit; remove local path.
- Run `lake update gaussian-field` to drop local cache.
- Final clean `lake build`.
- Update `status.md`, `README.md` counts.

## Total estimate
**3-4 active days, 1 week wall-clock.**

## Dependencies

Track 2 is **independent** of Track 1 (FieldDecomposition.lean rewrite).
Either order works. Doing Track 2 first means Track 1 can later import
the d-dim DFT machinery directly from gaussian-field.

## Risks
1. **Naming clashes** in gaussian-field — `latticeFourierProductBasisFun`
   may collide with internal names. Likely a non-issue but check.
2. **Import cycles** — gaussian-field's `Lattice/Covariance.lean` already
   uses `lattice_covariance_eq_spectral` which uses `massEigenvalues`.
   New family proofs use `lattice_covariance_eq_spectral` too, so import
   ordering needs care. Should be fine in a fresh file.
3. **d=2 consumers in gaussian-field** that use the specialized versions
   — need to update or alias.

---

# Future: split gaussian-field into two packages

After Track 2, gaussian-field naturally cleaves into two concerns:

## Package A: `lattice-spectrum` (or similar name)
Pure linear algebra / spectral theory on a finite lattice torus.
- `Lattice/Laplacian.lean` — lattice Laplacian, eigenvalue formulas
  (`latticeEigenvalue1d`, `latticeLaplacianEigenvalue`, `latticeEigenvalue`)
- `Lattice/SpectralCovariance.lean` — `massMatrixHerm`, `massEigenvalues`,
  `massEigenvectorBasis`, `spectralLatticeCovariance`
- `Lattice/CirculantDFT*.lean` — DFT diagonalization (1d, 2d, family)
- (After Track 2:) `Lattice/LatticeFourierProduct.lean`,
  `Lattice/LatticeFourierIndexing.lean`
- `Lattice/Covariance.lean` — lattice covariance kernels

No Gaussian/probability content. Pure spectral theory.

## Package B: `gaussian-field` (slimmed)
Abstract Gaussian measures + cylinder algebra + Schwartz-nuclear.
- `GaussianField/*.lean` — abstract Gaussian measures, characteristic
  functionals, `IsGaussian`, etc.
- `Cylinder/*.lean` — cylinder set algebra
- `SchwartzNuclear/*.lean` — nuclear Schwartz space machinery
- `Density.lean`, `Hypercontractive.lean`, `WickMultivariate.lean`,
  `StandardGaussianBridge.lean` — the Gaussian-measure side

Depends on `lattice-spectrum` (lightly) for the lattice-Gaussian
specializations like `latticeGaussianMeasure`.

## Why split?
1. **Separation of concerns.** Spectral theory ≠ probability.
2. **Reusability.** `lattice-spectrum` is useful for sibling projects
   (lattice gauge theory, transfer matrix, etc.) that don't need
   Gaussian measures.
3. **Smaller dependency footprint.** Probability stack is heavy in
   Mathlib; `lattice-spectrum` could avoid it entirely.
4. **Independent evolution.** The lattice-spectrum API is stable; the
   Gaussian/probability side is more likely to evolve.

## Estimate
**~1-2 weeks active, 2-4 weeks wall-clock.** Mostly mechanical (file
moves, import updates). Bigger work item: deciding the API boundary
(does `latticeCovariance` live in lattice-spectrum or gaussian-field?
probably the abstract CLM stays in gaussian-field but the spectral
forms cross the boundary).

This is a longer-term hygiene project, separate from Track 2 but
naturally enabled by it (Track 2 makes the boundary visible).
