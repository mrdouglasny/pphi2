# Refactor plan: discharge GJ-form sorry — final version (v3) [COMPLETED]

> **STATUS: IMPLEMENTED** (Track 1 + Track 2 both done):
> - `3e0e962` — *Rewrite FieldDecomposition via product DFT basis* (Track 1)
> - `1a26483` — *Track 2: move generic d-dim DFT machinery to gaussian-field*
> - `8ba92f7` — *NelsonEstimate/FieldDecomposition: remove false GJ-form theorem + bridge sorry*
> - `de5edcb` — *cleanup: drop unused DFT duplicate from Pphi2/GeneralResults*
>
> The post-refactor `FieldDecomposition.lean` uses `latticeFourierProductBasisFun`
> (now living in upstream `gaussian-field/Lattice/LatticeFourierProduct.lean` after
> Track 2). The false `massEigenvalues_eq_latticeEigenvalue` bridge is removed;
> the `canonicalSumFieldFunction_covariance_eq_GJ` theorem is gone, replaced by
> the still-correct variance theorem `canonicalSumFieldFunction_covariance`.
> All downstream work (e.g. `RoughErrorBound.lean`'s `canonicalCrossTerm` /
> `canonicalRoughError` and the `canonical-2site-wick-formula-plan.md`)
> is built on top of this post-refactor structure.
>
> Doc kept for historical reference; the plan body below describes the
> design that has now been executed.
>
> **History:**
> - v1: replace matrix-spectral defs with explicit DFT in gaussian-field.
> - v2: refined with separation-of-variables design, direct pointwise basis,
>   `Basis.ext` for `MΣ=I`.
> - **v3 (current):** Codex review found that pphi2 already has a complete
>   generic d-dim DFT machinery (`LatticeProductDFT.lean`,
>   `LatticeFourierIndexing.lean`) with proper Nyquist normalization.
>   Rewriting it in gaussian-field would duplicate work. Instead, fix the
>   inconsistency in `FieldDecomposition.lean` itself: reindex the
>   canonical fields to use the existing DFT-product basis, then discharge
>   the GJ form via `abstract_spectral_eq_dft_spectral_family`.

## The mathematical bug

The currently-sorry'd bridge `massEigenvalues k = latticeEigenvalue d N a mass (Fintype.equivFin k)` is **provably false**:

- Mathlib's `Matrix.IsHermitian.eigenvalues` is defined via `eigenvalues₀ : Fin (Fintype.card n) → ℝ` which is `Antitone` (sorted by real value, decreasing).
- `latticeEigenvalue ∘ Fintype.equivFin` is in lex order over `FinLatticeSites d N = Fin d → ZMod N`.
- Same multiset of eigenvalues, but the per-`k` identity holds only up to a permutation that's neither the identity nor `Fintype.equivFin`.

The committed GJ-form proof depends on this false bridge through a
`convert ... using 8 <;> Subsingleton.elim` hack and is therefore mathematically suspect — *the GJ form theorem is "proved" by appealing to a false lemma.*

The variance theorem `canonicalSumFieldFunction_covariance` is stated in a form that's a true sum identity, but its RHS likely doesn't equal the Glimm–Jaffe heat-kernel-cutoff GFF covariance — because the canonical smooth field's eigenvectors (matrix-spectral basis, sorted) and weights (formula at integer index, lex) are mismatched.

## Fix: reframe `FieldDecomposition.lean` using the existing DFT machinery

### Existing pphi2 generic infrastructure (all proved theorems, no axioms/sorries)

In `Pphi2/GeneralResults/LatticeProductDFT.lean`:
- `latticeFourierProductBasisFun N d m : FinLatticeSites d N → ℝ := ∏ i, latticeFourierBasisFun N (m i) (x i)` — d-dim product basis indexed by `m : Fin d → Fin N`.
- `latticeFourierProductNormSq N d m := ∏ i, latticeFourierNormSq N (m i)` — handles Nyquist mode normalization (norm 2, not 1).
- `latticeFourierProductCoeff N d f m := Σ_x f(x) · basisFun(m, x)` — DFT coefficient.
- `dft_parseval_family` — d-dim Parseval at the inner-product level.
- `massOperator_product_eigenvector_family` — the **eigenvector property**: `M (basisFun m) = (Σ_i latticeEigenvalue1d N a (m i) + mass²) · basisFun(m)`. Eigenvalue and eigenvector consistently indexed by the multi-index `m`.
- `dft_eigencoeff_massOperator_family`.
- `abstract_spectral_eq_dft_spectral_family` — the bridge: `covariance latticeCovariance f g = Σ_m coeff(f,m)·coeff(g,m) / ((Σ_i latticeEigenvalue1d N a (m i) + mass²) · latticeFourierProductNormSq N d m)`.

In `Pphi2/GeneralResults/LatticeFourierIndexing.lean`:
- `realModeRawEquivFamily : (Fin d → Fin N) ≃ (Fin d → Fin N)` — bridge between raw and pairing-via-fourierFreq mode indexings.
- `sum_latticeEigenvalue_eq_sum_latticeEigenvalue1d_family` — sum-level reindexing of `latticeEigenvalue d N a mass m` over integer indices into a sum over `Fin d → Fin N` of summed 1d eigenvalues.

In gaussian-field's `Lattice/Covariance.lean`:
- `latticeCovariance_GJ_eq_inv_smul_bare` — `latticeCovarianceGJ = (a^d)⁻¹ • latticeCovariance`.

### The rewrite

1. Add `import Pphi2.GeneralResults.LatticeProductDFT` to `FieldDecomposition.lean`.

2. Reindex the canonical types from `FinLatticeSites d N` to `Fin d → Fin N`:
   ```lean
   abbrev CanonicalJoint (d N : ℕ) [NeZero N] : Type :=
     ((Fin d → Fin N) → ℝ) × ((Fin d → Fin N) → ℝ)
   ```

3. Define a per-mode eigenvalue helper:
   ```lean
   def canonicalEigenvalue (d N : ℕ) [NeZero N] (a mass : ℝ) (m : Fin d → Fin N) : ℝ :=
     (∑ i, latticeEigenvalue1d N a (m i)) + mass^2
   ```
   And the smooth/rough split:
   ```lean
   theorem canonicalEigenvalue_split (m : Fin d → Fin N) (T : ℝ) :
       (canonicalEigenvalue d N a mass m)⁻¹ =
         exp(-T·λ_m)/λ_m + (1-exp(-T·λ_m))/λ_m  := by ... unfold + algebra
   ```

4. Reframe the field functions to use `latticeFourierProductBasisFun N d m`:
   ```lean
   def canonicalSmoothFieldFunction (η : CanonicalJoint d N) : FinLatticeSites d N → ℝ :=
     fun x => (Real.sqrt (a^d))⁻¹ *
       ∑ m : Fin d → Fin N,
         Real.sqrt (C_S m / latticeFourierProductNormSq N d m) *
         latticeFourierProductBasisFun N d m x *
         η.1 m
   ```
   The division-by-norm is absorbed into the weight; the basis vector itself can be non-unit-norm (e.g., norm² = 2 for Nyquist). With `η.1(m) ~ N(0,1)`, this gives the correct per-mode variance contribution.

5. Adapt the existing helpers (linearity, measurability, marginal-integral-zero, self-moment, cross-moment-zero) to the new index. The `pi_gaussian_*` lemmas are generic over the index type and need no changes.

6. Re-prove the variance theorem:
   ```
   ∫ φ(η)(x) · φ(η)(y) ∂μ_joint
     = (a^d)⁻¹ · Σ_m basisFun(m,x) · basisFun(m,y) / (λ_m · N_m)
   ```
   Proof: 4-term distribute, cross terms vanish by independence (Fubini),
   SS and RR via `pi_gaussian_bilinear_moment`, combine via `canonicalEigenvalue_split`.

7. Discharge the GJ form via `abstract_spectral_eq_dft_spectral_family`:
   ```
   covariance latticeCovariance δ_x δ_y = Σ_m coeff(δ_x,m) · coeff(δ_y,m) / (λ_m · N_m)
                                        = Σ_m basisFun(m,x) · basisFun(m,y) / (λ_m · N_m)
   ```
   (using `coeff(δ_x, m) = basisFun(m, x)` via `Finset.sum_eq_single`).
   Then multiply by `(a^d)⁻¹` and apply `latticeCovariance_GJ_eq_inv_smul_bare`:
   ```
   covariance latticeCovarianceGJ δ_x δ_y = (a^d)⁻¹ · covariance latticeCovariance δ_x δ_y
                                          = (a^d)⁻¹ · Σ_m basisFun(m,x) · basisFun(m,y) / (λ_m · N_m)
                                          = LHS  [by variance theorem]
   ```

8. Remove the sorry'd `massEigenvalues_eq_latticeEigenvalue` bridge. It's not needed anymore — the variance theorem and GJ form are now proved without appealing to the false per-mode identity.

## Out of scope (for now)

`gaussian-field` is left alone. Its `massEigenvalues`/`massEigenvectorBasis` retain their abstract matrix-spectral definitions, which are correct and used elsewhere (for properties like positivity that don't depend on per-mode indexing).

## Track 2 (later, optional)

Move the generic d-dim DFT machinery (`LatticeProductDFT.lean`, `LatticeFourierIndexing.lean`) from pphi2 into gaussian-field. This is a hygiene/Mathlib-ready cleanup — those theorems are about gaussian-field's primitives (lattice mass operator + DFT diagonalization) and morally belong upstream. ~15-20 theorem migration. Total: ~3 days, not blocking.

## Estimate

**Track 1: ~2 days active, ~3-5 days wall-clock.**
**Track 2: ~3 days active (optional cleanup, separate commit).**

## Validation gates

- After step 4: `lake env lean Pphi2/NelsonEstimate/FieldDecomposition.lean` compiles up to the helper layer.
- After step 6: variance theorem compiles.
- After step 7: GJ form compiles.
- After step 8: 0 sorries in `FieldDecomposition.lean`.
- Final: `lake build` passes.

## Risk register (revised)

1. ~~`OrthonormalBasis.tensorProduct` complexity~~ — moot; we use `latticeFourierProductBasisFun` which is *not* an orthonormal basis (Nyquist normalization), but its norm-squared `latticeFourierProductNormSq` is tracked explicitly and divides out cleanly.

2. ~~Mathlib `Matrix.IsHermitian` infrastructure~~ — moot; we don't touch gaussian-field.

3. **Existing `canonicalSmoothFieldFunction` etc. consumers.** This file's definitions are used elsewhere in pphi2 (FKG measurability, etc.). The reindex from `FinLatticeSites d N` to `Fin d → Fin N` is a breaking change in the η-coord type. Mitigation: keep the old definitions alongside (perhaps as `legacy_canonicalSmoothFieldFunction`), prove the new variance theorem in terms of the new ones, and update only `canonicalSumFieldFunction_covariance_eq_GJ` to use the new variance theorem.

4. **Variance theorem name collision.** If the old `canonicalSumFieldFunction_covariance` is used elsewhere in pphi2 (it shouldn't be — it's brand new), keep the old form too.

The architecture is now clean and the false bridge is properly removed.
