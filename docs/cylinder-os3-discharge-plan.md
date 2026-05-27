# OS3 (reflection positivity) discharge plan — isotropic cylinder construction

*2026-05-27. How to discharge the `hRP` hypothesis of `cylinderIso_OS_of_RP_OS2`
(`Pphi2/AsymTorus/AsymContinuumLimit.lean`) — i.e. prove reflection positivity for the isotropic
`Z_Nt × Z_Ns` interacting measures, rather than assuming it. Confirmed feasible by external review
(2026-05-27): "Lattice RP → Pullback → Weak Limit is structurally perfect; RP is a closed condition
(`⟨ΘF, F⟩ ≥ 0`) that survives weak convergence natively."*

## The target

```
hRP : ∀ (Lt) (hLt) (μ), CylinderMeasureSequenceEventuallyReflectionPositive Ls
        (fun n => cylinderPullbackMeasure (Lt n) Ls (μ n))
```

For the family produced by `asymTorusIso_cylinderUniformGreenBound`: cylinder pullbacks of the iso
UV-limit torus measures `μ n` are eventually reflection-positive (matrixwise).

## What is ALREADY proved (the downstream half — no new work)

The IR→cylinder transfer of RP is **done** in `Pphi2/IRLimit/CylinderOS.lean`:

- `cylinderMeasureReflectionPositive_of_tendsto_cf` (CylinderOS.lean:404) — **theorem**: if a sequence
  `νseq k → ν` in characteristic functionals and each fixed RP matrix is *eventually* `≥ 0`, then `ν`
  is reflection positive. (RP survives the weak limit — proved via `ge_of_tendsto` on the finite
  matrix sum.)
- `CylinderMeasureSequenceEventuallyReflectionPositive.of_forall` (CylinderOS.lean:334) — full RP at
  every index ⟹ the eventual-matrixwise input.
- OS2 invariance (time reflection + translations) passes through the torus→cylinder pullback
  (`cylinderPullback_timeReflection_invariant`, CylinderOS.lean:109–123) — proved.

So once we have **lattice-level RP** for the iso interacting measure, the rest composes.

## The crux: heterogeneous lattice reflection positivity (the new work)

The square track has the full lattice-RP chain **proved** in `Pphi2/OSProofs/OS3_RP_Lattice.lean`,
for `FinLatticeSites 2 N = Fin 2 → Fin N`:

| Square lemma | File:line | Status | What it gives |
|---|---|---|---|
| `gaussian_rp_cov_perfect_square` | OS3_RP_Lattice.lean:648 | **private axiom** | Gaussian quadratic form `≥ 0` after block-zero Fubini factorization |
| `massOperator_cross_block_zero` | OS3_RP_Lattice.lean:406 | theorem | `Q_{x,y} = 0` for `x ∈ S₊`, `y ∈ Θ(S₊)` (nearest-neighbour ⟹ no cross-coupling) |
| `action_decomposition` (V = V₊+V₀+V₋) | OS3_RP_Lattice.lean:246–298 | theorem | split the interaction by time sign; `V₋ = V₊∘Θ` |
| `gaussian_rp_perfect_square` | OS3_RP_Lattice.lean:697 | theorem | boundary-weighted Gaussian RP |
| `gaussian_density_rp` | OS3_RP_Lattice.lean:788 | theorem | `∫ G·(G∘Θ)·w dμ_GFF ≥ 0` (Fubini via `piEquivPiSubtypeProd` + density factorization) |
| `gaussian_rp_with_boundary_weight` | OS3_RP_Lattice.lean:1022 | theorem | same at the measure level |
| `lattice_rp` | OS3_RP_Lattice.lean:1072 | theorem | **interacting** measure RP: `∫ F·(F∘Θ) dμ_int ≥ 0`, `F` positive-time |
| `lattice_rp_matrix` | OS3_RP_Lattice.lean:1345 | theorem | matrix form `∑ᵢⱼ cᵢcⱼ ∫ cos⟨φ, fᵢ−Θfⱼ⟩ dμ_int ≥ 0` |

**Reflection setup (square):** `timeReflection2D : (t,x) ↦ (−t, x)` on `ZMod N × ZMod N`; positive
time `S₊ = {(t,x) : 0 < t.val < N/2}`; needs `N` even (so `N/2` boundary exists and `Θ` has no
fixed-site issues).

### Port to `Z_Nt × Z_Ns`

The interacting measure side is already isotropic (`interactingLatticeMeasureAsym`,
`latticeGaussianMeasureAsym`, `massOperatorAsym`). The port replaces `FinLatticeSites 2 N` by
`AsymLatticeSites Nt Ns = ZMod Nt × ZMod Ns` and reflects in the **time** factor `ZMod Nt`:

New lemmas to add (new file `Pphi2/OSProofs/OS3_RP_AsymLattice.lean`), mirroring the square chain:

1. `timeReflectionAsym : ZMod Nt × ZMod Ns → ZMod Nt × ZMod Ns`, `(t, x) ↦ (−t, x)`; `fieldReflectionAsym`.
   Positive-time region `S₊ = {(t,x) : 0 < t.val < Nt/2}`. **Requires `Even Nt`** — already ensured
   by the IR-family construction (`Nt_k = 2(n+1)(k+1)`; see `AsymContinuumLimit.lean`).
2. `massOperatorAsym_cross_block_zero` — `(massOperatorMatrixAsym)_{x,y} = 0` for `x ∈ S₊`,
   `y ∈ Θ S₊`. Follows from the nearest-neighbour structure of `finiteLaplacianAsymFun` (only `t±1`
   couplings in time): the positive-time interior never couples across the reflection plane. (The
   `asym_direction_sum`/circulant lemmas in gaussian-field `AsymCovariance.lean` are the building
   blocks; this is the genuinely lattice-specific input.)
3. `action_decomposition_asym` — `V_a = V₊ + V₀ + V₋` with `V₋ = V₊ ∘ Θ`. The interaction
   `interactionFunctionalAsym = a²·Σ_x :P:` splits over the disjoint time regions `S₊ / S₀ / S₋`
   exactly as in the square (it is a sum of single-site terms, so the split is by partitioning the
   site set — should port near-verbatim).
4. `gaussian_density_rp_asym`, `gaussian_rp_with_boundary_weight_asym`, `lattice_rp_asym`,
   `lattice_rp_matrix_asym` — port the Fubini / density-factorization / cos-expansion proofs.
5. **Reuse** `gaussian_rp_cov_perfect_square` (the private Gaussian-quadratic-form axiom) — adapt its
   shape to the `Z_Nt × Z_Ns` precision matrix (or generalize it once; it is the only axiom in the
   chain, everything else is proved).

### Composition (lattice RP ⟹ `hRP`)

1. `lattice_rp_matrix_asym` ⟹ matrixwise RP of `interactingLatticeMeasureAsym Nt Ns …`.
2. Push through the embedding `asymTorusEmbedLiftIso` (positivity preserved — the RP matrix entries
   are `∫ cos⟨φ, …⟩`, and `(ι ω)(f) = ω(asymLatticeTestFnIso f)`, so the torus-test-function RP
   matrix equals a lattice RP matrix). ⟹ RP of `asymTorusInteractingMeasureIso` at each `(Nt,Ns,a)`.
3. UV continuum limit (`a → 0`): RP of the torus matrices is `≥ 0` at every `k`, so (closed
   condition) the UV-limit torus measure `μ n` is RP — OR carry the matrixwise `≥ 0` through the
   `cylinderMeasureReflectionPositive_of_tendsto_cf`-style transfer already used.
4. Cylinder pullback + IR weak limit: `CylinderMeasureSequenceEventuallyReflectionPositive.of_forall`
   + `cylinderMeasureReflectionPositive_of_tendsto_cf` (both proved) close `hRP`.

The positive-time test functions must map correctly: `cylinderPositiveTimeSubmodule` →
`asymTorus` positive-time → lattice `S₊`. The reflection operators
`cylinderTimeReflection` / `asymTorusTimeReflection` already exist (gaussian-field
`Cylinder/Symmetry.lean`, `Torus/AsymmetricTorus.lean`) and reflect the time factor — they line up
with `timeReflectionAsym` under the embedding.

## Prerequisite: narrow `hRP`/`hOS2` to the constructed family

`cylinderIso_OS_of_RP_OS2` currently takes `hRP`/`hOS2` `∀`-quantified over *all* families, which a
genuine OS3 proof cannot supply (it proves RP only for the specific even-`Nt` family). Before
discharging, expose the IR family from `asymTorusIso_cylinderUniformGreenBound` as a named `def`
(or restructure so the family is in scope) and narrow the hypotheses to it. Then the discharged
lattice RP for that family plugs straight in. (See `cylinder-conditional-inputs-provability.md` §5.)

## Effort & alternatives

- **Main route (port the square chain): large — ~2000 lines**, parallel to OS3_RP_Lattice.lean
  (lines 246–1363). Mostly mechanical (the square proofs are detailed and structurally portable),
  with one genuinely-new lattice lemma (`massOperatorAsym_cross_block_zero`) and the reuse/adapt of
  the private `gaussian_rp_cov_perfect_square` axiom.
- **Even-`Nt`** is required and already guaranteed by the IR construction; thread `Even Nt` (and
  `Even Ns` is free in the current sequence) into the reflection definitions.
- **Alternative (transfer-matrix):** RP for the cylinder follows from Osterwalder–Seiler positivity
  of the transfer matrix `e^{-aH_{Ls}}`; this is the same Perron–Frobenius/transfer-matrix structure
  flagged for the §4 moment bound, so a single transfer-matrix-positivity development could serve
  both OS3 and the §4 discharge. Worth scoping jointly if both are pursued.
- **Keep as hypothesis:** OS3 is an *independent, standard* input (positivity, not integrability);
  leaving `hRP` as an explicit hypothesis is legitimate, exactly as the square track leaves its RP
  resting on the one `gaussian_rp_cov_perfect_square` axiom. The isotropic OS3 is no harder than the
  square's (which is proved modulo that one axiom).

## Summary

The downstream RP-transfer machinery (weak-limit inheritance, OS2-through-pullback) is **proved**.
The only substantial new work is **porting the square lattice-RP chain to `Z_Nt × Z_Ns`** (one new
lattice lemma `massOperatorAsym_cross_block_zero` + mechanical ports + reuse of the one
`gaussian_rp_cov_perfect_square` axiom), then narrowing `hRP` to the constructed even-`Nt` family.
No genuinely new mathematics beyond the square track; the even-`Nt` requirement is already met.
