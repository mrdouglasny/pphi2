# Cylinder via an isotropic `Z_m × Z_n` lattice — redesign plan

*2026-05-26. The current asymmetric-torus construction discretizes the rectangular torus
`T = S¹(Lt) × S¹(Ls)` on an `N×N` lattice with a single **geometric-mean** spacing
`a_geom = √(Lt·Ls)/N`. A deep-think vet (and a Fourier check) showed this is **metric-inconsistent**:
it is really a *square* torus of side `√(Lt·Ls)` with the rectangle injected only through the
evaluation, so the lattice second moment converges to the **wrong** Green's function
(`4π²(p²+q²)/(Lt·Ls)` instead of the correct `(2πp/Lt)²+(2πq/Ls)²`), the convergence to
`asymTorusContinuumGreen` is **false** for `Lt≠Ls`, and the would-be uniform constant **diverges as
`Lt→∞`**, breaking the cylinder IR limit. This doc redesigns the lattice to be manifestly correct.*

## The correct discretization (isotropic spacing, rectangular extent)

The continuum operator `−Δ + m² = −∂_x² − ∂_y² + m²` is **isotropic**; the only anisotropy is the
**boundary condition** (periods `Lt`, `Ls`, i.e. allowed momenta `2π/Lt`, `2π/Ls`). So discretize with a
**single isotropic spacing `a`** and **different site counts per direction**:
```
lattice = Z_{Nt} × Z_{Ns},   Nt = Lt/a,  Ns = Ls/a   (so a = Lt/Nt = Ls/Ns).
```
The lattice Laplacian is the standard nearest-neighbour `−Δ_a` with the *same* `1/a²` in both
directions (isotropic); the rectangle is carried entirely by `Nt ≠ Ns`. As `a→0` (`Nt,Ns→∞` with
`Nt/Ns = Lt/Ls`) the eigenvalues converge to the **correct** rectangular symbol:
```
(2/a²)(1−cos 2πp/Nt) + (2/a²)(1−cos 2πq/Ns)  →  (2πp/Lt)² + (2πq/Ls)²,
```
matching `asymTorusContinuumGreen` exactly, with constants **uniform in `Lt`** (no `√(Lt·Ls)` metric
distortion). This is the standard lattice-field-theory discretization of a rectangular torus.

## What already exists in gaussian-field (reuse, don't rebuild)

- **The heterogeneous lattice type**: `AsymLatticeSites Nt Ns = ZMod Nt × ZMod Ns`
  (`Torus/AsymmetricTorus.lean:69`) — exactly `Z_m × Z_n`.
- **The per-direction evaluation**: `evalAsymTorusAtSite Nt Ns` (`:90`) "restricts to the time lattice
  with spacing `Lt/Nt` and the space lattice with spacing `Ls/Ns`." **At `Nt/Ns = Lt/Ls` these spacings
  coincide (`= a`) and the evaluation is automatically isotropic** — no change needed.
- **Embedding / symmetries**: `asymTorusEmbedCLM`, `asymTorusTranslation`, `asymTorusTimeReflection`,
  `asymTorusSwap` (`:104,130,142,154`).
- **Rectangular DFT**: `Lattice/CirculantDFT2d.lean`, `Lattice/LatticeFourierIndexing.lean` — the
  spectral machinery for `ZMod Nt × ZMod Ns`.

So the correct construction is mostly **using the existing `AsymLatticeSites Nt Ns` machinery at
`Nt/Ns = Lt/Ls`**, not new infrastructure.

## What pphi2 does wrong (the thing to replace)

`AsymTorus/AsymTorusEmbedding.lean` defines `finToAsymSite : FinLatticeSites 2 N → AsymLatticeSites N N`
(collapsing to `Nt = Ns = N`) and `asymGeomSpacing = √(Lt·Ls)/N`, feeding the **square**
`latticeCovarianceGJ 2 N (asymGeomSpacing …)`. So the covariance is the *square*-`√(Lt·Ls)` lattice's,
while the evaluation is rectangular — the inconsistency. **Replace** `finToAsymSite` + `asymGeomSpacing`
with the `AsymLatticeSites Nt Ns` (`Nt/Ns = Lt/Ls`) construction and an **isotropic single-spacing**
covariance.

## What needs building

1. **Heterogeneous-lattice covariance** on `AsymLatticeField Nt Ns`: the isotropic lattice resolvent
   `(−Δ_a + m²)⁻¹` on `ZMod Nt × ZMod Ns`, single spacing `a`. The square machinery
   (`latticeCovariance d N`, circulant DFT) is built on `FinLatticeField d N`; generalize to the
   product `ZMod Nt × ZMod Ns` using the existing `CirculantDFT2d` (the spectral form is a product of
   two 1D circulant DFTs of sizes `Nt`, `Ns` — already the right shape).
2. **The convergence (now a clean, TRUE port)**: `σ²_{Nt,Ns}(f,g) → asymTorusContinuumGreen(f,g)`. With
   the isotropic spacing it factors per direction into 1D circles `S¹(Lt)` (size `Nt`, spacing `a`) and
   `S¹(Ls)` (size `Ns`, spacing `a`); reuse gaussian-field's per-1D-direction lattice→continuum
   convergence + Tannery, exactly as `torus_propagator_convergence` (`TorusPropagatorConvergence.lean:547`)
   does for the square case. This is now mathematically true (the `Lt≠Ls` obstruction is gone) and is the
   honest version of the cyl-os0 "delta."
3. **pphi2 refactor of `AsymTorus/`**: re-target `asymTorusEmbedLift`, the cutoff exp-moment bound, the
   Nelson estimate, and the uniform second-moment bound to the `Z_{Nt}×Z_{Ns}` isotropic lattice. The
   Nelson cell-area input (`a² = a_t·a_s` previously `= Lt·Ls/N²`) is now `a²` with `a = Lt/Nt = Ls/Ns`
   — *more* natural (the volume is `Nt·Ns·a² = Lt·Ls`). `IRLimit/` is abstract (0-axiom) and just
   re-targets to the new lattice family.

## The cylinder limit becomes natural

The cylinder `S¹(Ls) × ℝ` is the **`Nt → ∞` limit at fixed `Ns`, fixed `a`** (time circle `Lt = Nt·a →
∞` decompactifies to `ℝ`; space stays `S¹(Ls)`), then `a→0` (`Ns→∞`). With the isotropic lattice both
limits are metric-consistent and the constants are uniform in `Nt` (= uniform in `Lt`) — exactly what
`AsymTorusSequenceHasUniformGreenMomentBound` needs. The `Z_{Nt}×Z_{Ns}` lattice with `Nt→∞` is also the
natural **transfer-matrix** picture (spatial circle `Z_{Ns}`, time `ℤ`), connecting to the cyl-2 OS4
work and the rg/ TRG program.

## Order of work

1. **gaussian-field**: isotropic single-spacing covariance on `AsymLatticeField Nt Ns` (via
   `CirculantDFT2d`), and the convergence `σ²_{Nt,Ns} → asymTorusContinuumGreen` (port of
   `lattice_green_tendsto_continuum`, now per-direction with common spacing `a`, two circle sizes).
2. **pphi2 `AsymTorus/`**: replace `finToAsymSite`/`asymGeomSpacing` with the `Nt/Ns = Lt/Ls` isotropic
   construction; re-derive cutoff bound + Nelson + second-moment on the new lattice.
3. **Assemble** `MeasureHasGreenMomentBound` (now a true theorem, not an axiom) from the cutoff bound +
   the (now true) convergence + the limit transfer; feed `routeBPrime_cylinder_OS`.

This **supersedes** `asymGeomSpacing`, the `cyl-1a-bridge-plan.md` BD route, and the cyl-os0 "vetted
axiom" option: with the correct lattice the OS0 convergence is **true and provable**, so no axiom is
needed. (Records the vet finding: the geometric-mean construction was metric-inconsistent.)
