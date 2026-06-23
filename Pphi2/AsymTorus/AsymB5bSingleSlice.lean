/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.AsymTorus.AsymBridgeKLimit

/-!
# Layer-B2 Route A, Piece 4: B5b single-slice stability

This file isolates the single-time-slice input needed after the Piece-3
`K -> infinity` bridge.

The Route-A bound from Pieces 1-3 has the schematic form

```
∫ (Σ_t <g_t, ψ_t>)^2 d(pathMeasure)
  <= (2 / (1 - γ)) * Σ_t Var_Ω(g_t) + remainder.
```

Piece 4 replaces each ground-state single-slice variance by the matching free
single-slice covariance quantity, with a constant independent of `a` and `Nt`
at fixed `Ls`.

## A-power audit

The formal free slice object below is not an informal `Q^{-1}` placeholder.  It
is the one-slice lift into the already-existing GJ-normalized lattice covariance
`latticeCovarianceAsymGJ`.  This matters because `latticeCovarianceAsymGJ` is a
covariance *factorization* operator with the `a^{-1}` GJ normalization built in.
Thus a slice test vector `g_t = a • δ_site` contributes exactly an `a^2` factor
on the test-function side, cancelling the `(a^{-1})^2` in the GJ covariance
form.  This is the same square-root convention whose misread caused the earlier
crux-2 `a`-power error; see `docs/crux2-energy-factorization.md`.

The analytic B5b statement is kept as a deliberately narrow axiom:
`groundVariance_le_freeCovariance`.  It is the `Ls`-fixed, single-slice
specialization of the Nelson/chessboard estimate (`asymNelson_exponential_estimate_iso`),
not a new volume theorem.
-/

noncomputable section

open MeasureTheory GaussianField
open scoped BigOperators

namespace Pphi2

variable {Nt Ns : ℕ} [NeZero Nt] [NeZero Ns]

local notation "ν" => (volume : Measure (SpatialField Ns))

/-! ## Single-slice covariance bookkeeping -/

/-- A time-family supported on one slice. -/
def singleSliceFamily (t : ZMod Nt) (g : SpatialField Ns) :
    ZMod Nt → SpatialField Ns :=
  fun s => if s = t then g else 0

/-- Lift a spatial test vector to a spacetime lattice test vector supported on
one time slice.  Using `asymSliceEquiv.symm` keeps the spatial `Fin Ns` reindex
and the spacetime lattice conventions definitional. -/
noncomputable def singleSliceLatticeField (t : ZMod Nt) (g : SpatialField Ns) :
    AsymLatticeField Nt Ns :=
  (asymSliceEquiv Nt Ns).symm (singleSliceFamily (Nt := Nt) (Ns := Ns) t g)

/-- Ground-state single-slice second moment.  This is the quantity supplied by
Piece 1 after the perpendicular projection is contracted away:
`||P_1(M_g Ω)||^2 <= groundSliceVariance g`.

For the even `P(φ)_2` application this is the centered variance after the usual
field-odd mean-zero identification; the formal Route-A bound only needs this
uncentered second moment. -/
noncomputable def groundSliceVariance
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (g : SpatialField Ns) : ℝ :=
  ∫ ψ, (asymSliceObsLinear g ψ) ^ 2 *
      ((asymGroundVector Nt Ns P a mass ha hmass) ψ) ^ 2 ∂ν

/-- The free covariance of a one-slice test vector, expressed in the existing
GJ-normalized lattice covariance form.  This is the Lean-facing representative
of the spatial free covariance in the B5b statement. -/
noncomputable def freeSingleSliceCovariance
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (t : ZMod Nt) (g : SpatialField Ns) : ℝ :=
  GaussianField.covariance (latticeCovarianceAsymGJ Nt Ns a mass ha hmass)
    (singleSliceLatticeField (Nt := Nt) (Ns := Ns) t g)
    (singleSliceLatticeField (Nt := Nt) (Ns := Ns) t g)

/-- Sum of the ground-state slice variances over a time family. -/
noncomputable def groundSliceVarianceSum
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (g : ZMod Nt → SpatialField Ns) : ℝ :=
  ∑ t : ZMod Nt, groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass (g t)

/-- Sum of one-slice free covariance quantities over a time family. -/
noncomputable def freeSingleSliceCovarianceSum
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (g : ZMod Nt → SpatialField Ns) : ℝ :=
  ∑ t : ZMod Nt, freeSingleSliceCovariance (Nt := Nt) (Ns := Ns) a mass ha hmass t (g t)

theorem freeSingleSliceCovariance_nonneg
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (t : ZMod Nt) (g : SpatialField Ns) :
    0 ≤ freeSingleSliceCovariance (Nt := Nt) (Ns := Ns) a mass ha hmass t g := by
  unfold freeSingleSliceCovariance GaussianField.covariance
  exact real_inner_self_nonneg

theorem freeSingleSliceCovarianceSum_nonneg
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (g : ZMod Nt → SpatialField Ns) :
    0 ≤ freeSingleSliceCovarianceSum (Nt := Nt) (Ns := Ns) a mass ha hmass g := by
  unfold freeSingleSliceCovarianceSum
  exact Finset.sum_nonneg fun t _ =>
    freeSingleSliceCovariance_nonneg (Nt := Nt) (Ns := Ns) a mass ha hmass t (g t)

omit [NeZero Nt] [NeZero Ns] in
@[simp] theorem singleSliceFamily_smul (t : ZMod Nt) (c : ℝ) (g : SpatialField Ns) :
    singleSliceFamily (Nt := Nt) (Ns := Ns) t (c • g) =
      c • singleSliceFamily (Nt := Nt) (Ns := Ns) t g := by
  funext s i
  by_cases h : s = t <;> simp [singleSliceFamily, h]

@[simp] theorem singleSliceLatticeField_smul (t : ZMod Nt) (c : ℝ) (g : SpatialField Ns) :
    singleSliceLatticeField (Nt := Nt) (Ns := Ns) t (c • g) =
      c • singleSliceLatticeField (Nt := Nt) (Ns := Ns) t g := by
  unfold singleSliceLatticeField
  rw [singleSliceFamily_smul]
  exact map_smul ((asymSliceEquiv Nt Ns).symm : (ZMod Nt → SpatialField Ns) →ₗ[ℝ]
    AsymLatticeField Nt Ns) c (singleSliceFamily (Nt := Nt) (Ns := Ns) t g)

/-- The a-power ledger for one slice: scaling the spatial test vector by `c`
scales the free covariance by `c^2`.  In particular `g_t = a • δ_site` brings
exactly the `a^2` factor that cancels the GJ covariance's `(a^{-1})^2`. -/
theorem freeSingleSliceCovariance_smul
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (t : ZMod Nt) (c : ℝ) (g : SpatialField Ns) :
    freeSingleSliceCovariance (Nt := Nt) (Ns := Ns) a mass ha hmass t (c • g) =
      c ^ 2 * freeSingleSliceCovariance (Nt := Nt) (Ns := Ns) a mass ha hmass t g := by
  unfold freeSingleSliceCovariance GaussianField.covariance
  rw [singleSliceLatticeField_smul]
  rw [map_smul, inner_smul_left, inner_smul_right]
  simp [sq, mul_assoc]

/-! ## B5b analytic input -/

/-- **B5b single-slice stability** (analytic axiom, narrow form).

At fixed spatial circumference `Ls`, the ground-state one-slice second moment
is bounded by the free one-slice covariance with a constant independent of
`a`, `Nt`, and the time slice.  This is the `Ls`-fixed single-time-slice
specialization of the existing Nelson engine
`asymNelson_exponential_estimate_iso`; the intended discharge is to specialize
the Nelson/chessboard estimate before any time-volume summation.

Audit notes for discharge:
* keep `latticeCovarianceAsymGJ` as a square-root/factorization operator;
* prove the spatial covariance identification after the one-slice lift, not by
  replacing `T` with `Q^{-1}` by notation;
* recheck the `g_t = a • δ_site` case against
  `freeSingleSliceCovariance_smul` before removing this axiom. -/
axiom groundVariance_le_freeCovariance
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Ls : ℝ) (hLs : 0 < Ls) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
        (Ns : ℝ) * a = Ls →
        ∀ (t : ZMod Nt) (g : SpatialField Ns),
          groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass g ≤
            C * freeSingleSliceCovariance (Nt := Nt) (Ns := Ns) a mass ha hmass t g

/-- The chosen B5b constant. -/
noncomputable def groundVarianceFreeCovarianceConstant
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Ls : ℝ) (hLs : 0 < Ls) : ℝ :=
  Classical.choose (groundVariance_le_freeCovariance P mass hmass Ls hLs)

theorem groundVarianceFreeCovarianceConstant_pos
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Ls : ℝ) (hLs : 0 < Ls) :
    0 < groundVarianceFreeCovarianceConstant P mass hmass Ls hLs :=
  (Classical.choose_spec (groundVariance_le_freeCovariance P mass hmass Ls hLs)).1

theorem groundVariance_le_freeCovariance_with_constant
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Ls : ℝ) (hLs : 0 < Ls)
    (a : ℝ) (ha : 0 < a) (hvols : (Ns : ℝ) * a = Ls)
    (t : ZMod Nt) (g : SpatialField Ns) :
    groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass g ≤
      groundVarianceFreeCovarianceConstant P mass hmass Ls hLs *
        freeSingleSliceCovariance (Nt := Nt) (Ns := Ns) a mass ha hmass t g :=
  (Classical.choose_spec (groundVariance_le_freeCovariance P mass hmass Ls hLs)).2
    Nt Ns a ha hvols t g

/-- Sum B5b over time slices.  The constant is the same single-slice constant;
no `Nt` factor is introduced. -/
theorem groundVariance_sum_le_freeCovariance_sum
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Ls : ℝ) (hLs : 0 < Ls)
    (a : ℝ) (ha : 0 < a) (hvols : (Ns : ℝ) * a = Ls)
    (g : ZMod Nt → SpatialField Ns) :
    groundSliceVarianceSum (Nt := Nt) (Ns := Ns) P a mass ha hmass g ≤
      groundVarianceFreeCovarianceConstant P mass hmass Ls hLs *
        freeSingleSliceCovarianceSum (Nt := Nt) (Ns := Ns) a mass ha hmass g := by
  unfold groundSliceVarianceSum freeSingleSliceCovarianceSum
  calc
    ∑ t : ZMod Nt, groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass (g t)
        ≤ ∑ t : ZMod Nt,
            groundVarianceFreeCovarianceConstant P mass hmass Ls hLs *
              freeSingleSliceCovariance (Nt := Nt) (Ns := Ns) a mass ha hmass t (g t) := by
          exact Finset.sum_le_sum fun t _ =>
            groundVariance_le_freeCovariance_with_constant
              (Nt := Nt) (Ns := Ns) P mass hmass Ls hLs a ha hvols t (g t)
    _ = groundVarianceFreeCovarianceConstant P mass hmass Ls hLs *
          ∑ t : ZMod Nt,
            freeSingleSliceCovariance (Nt := Nt) (Ns := Ns) a mass ha hmass t (g t) := by
          rw [Finset.mul_sum]

/-! ## Combining with Piece 3 -/

/-- Turn a Piece-3 path-measure estimate into a free single-slice covariance
estimate.  The finite-`K`/DCT work is encapsulated in `hPiece3`; this theorem is
only the B5b substitution and remainder bookkeeping. -/
theorem piece3_pathMeasure_bound_to_freeCovariance_sum
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Ls : ℝ) (hLs : 0 < Ls)
    (a : ℝ) (ha : 0 < a) (hvols : (Ns : ℝ) * a = Ls)
    (g : ZMod Nt → SpatialField Ns)
    (γ rem C_rem_free : ℝ) (hγ : γ < 1)
    (hPiece3 :
      ∫ ψ : ZMod Nt → SpatialField Ns, (asymSliceFamilyLinear g ψ) ^ 2
          ∂((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt)
        ≤
      (2 / (1 - γ)) *
          groundSliceVarianceSum (Nt := Nt) (Ns := Ns) P a mass ha hmass g + rem)
    (hRem :
      rem ≤ C_rem_free *
        freeSingleSliceCovarianceSum (Nt := Nt) (Ns := Ns) a mass ha hmass g) :
      ∫ ψ : ZMod Nt → SpatialField Ns, (asymSliceFamilyLinear g ψ) ^ 2
          ∂((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt)
        ≤
      ((2 / (1 - γ)) * groundVarianceFreeCovarianceConstant P mass hmass Ls hLs +
          C_rem_free) *
        freeSingleSliceCovarianceSum (Nt := Nt) (Ns := Ns) a mass ha hmass g := by
  set A := 2 / (1 - γ)
  set CB5 := groundVarianceFreeCovarianceConstant P mass hmass Ls hLs
  set F := freeSingleSliceCovarianceSum (Nt := Nt) (Ns := Ns) a mass ha hmass g
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    have hden : 0 < 1 - γ := by linarith
    positivity
  have hB5sum :
      groundSliceVarianceSum (Nt := Nt) (Ns := Ns) P a mass ha hmass g ≤ CB5 * F := by
    dsimp [CB5, F]
    exact groundVariance_sum_le_freeCovariance_sum
      (Nt := Nt) (Ns := Ns) P mass hmass Ls hLs a ha hvols g
  calc
    ∫ ψ : ZMod Nt → SpatialField Ns, (asymSliceFamilyLinear g ψ) ^ 2
        ∂((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt)
        ≤ A * groundSliceVarianceSum (Nt := Nt) (Ns := Ns) P a mass ha hmass g + rem := by
          simpa [A] using hPiece3
    _ ≤ A * (CB5 * F) + C_rem_free * F := by
          exact add_le_add (mul_le_mul_of_nonneg_left hB5sum hA_nonneg) hRem
    _ = ((2 / (1 - γ)) * groundVarianceFreeCovarianceConstant P mass hmass Ls hLs +
          C_rem_free) *
        freeSingleSliceCovarianceSum (Nt := Nt) (Ns := Ns) a mass ha hmass g := by
          ring

/-- Lattice interacting second-moment version of
`piece3_pathMeasure_bound_to_freeCovariance_sum`.  This is the form closest to
the Layer-B2 assembly: Piece 3 supplies `hPiece3` on the path side, and B3
rewrites the interacting lattice second moment to that path integral. -/
theorem interacting_second_moment_bound_to_freeCovariance_sum
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Ls : ℝ) (hLs : 0 < Ls)
    (a : ℝ) (ha : 0 < a) (hvols : (Ns : ℝ) * a = Ls)
    (G : AsymLatticeField Nt Ns)
    (γ rem C_rem_free : ℝ) (hγ : γ < 1)
    (hPiece3 :
      ∫ ψ : ZMod Nt → SpatialField Ns,
          (asymSliceFamilyLinear ((asymSliceEquiv Nt Ns) G) ψ) ^ 2
          ∂((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt)
        ≤
      (2 / (1 - γ)) *
          groundSliceVarianceSum (Nt := Nt) (Ns := Ns) P a mass ha hmass
            ((asymSliceEquiv Nt Ns) G) + rem)
    (hRem :
      rem ≤ C_rem_free *
        freeSingleSliceCovarianceSum (Nt := Nt) (Ns := Ns) a mass ha hmass
          ((asymSliceEquiv Nt Ns) G)) :
      ∫ ω : Configuration (AsymLatticeField Nt Ns), (ω G) ^ 2
          ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass)
        ≤
      ((2 / (1 - γ)) * groundVarianceFreeCovarianceConstant P mass hmass Ls hLs +
          C_rem_free) *
        freeSingleSliceCovarianceSum (Nt := Nt) (Ns := Ns) a mass ha hmass
          ((asymSliceEquiv Nt Ns) G) := by
  have hpath :=
    piece3_pathMeasure_bound_to_freeCovariance_sum
      (Nt := Nt) (Ns := Ns) P mass hmass Ls hLs a ha hvols
      ((asymSliceEquiv Nt Ns) G) γ rem C_rem_free hγ hPiece3 hRem
  rw [asym_interacting_second_moment_eq_pathMeasure_slicePairing
    (Nt := Nt) (Ns := Ns) P a mass ha hmass G]
  refine le_trans ?_ hpath
  refine le_of_eq ?_
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun ψ => ?_
  have hlin := asymSliceFamilyLinear_eq_slicePairing ((asymSliceEquiv Nt Ns) G) ψ
  simpa using (congrArg (fun x : ℝ => x ^ 2) hlin).symm

/-- Final algebraic handoff: if a later free-side assembly identifies the sum
of one-slice free covariances with the full spacetime free variance (with
constant `C_free_assemble`), then the interacting lattice second moment is in
the exact free lattice covariance form.

The hypothesis `hFreeAssemble` is intentionally explicit.  A standalone
`1 / (1 - γ)` comparison is the known `a`-non-uniform trap; the free-side
assembly must be proved or separately vetted in the same a-power convention. -/
theorem interacting_second_moment_bound_to_lattice_free_covariance
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Ls : ℝ) (hLs : 0 < Ls)
    (a : ℝ) (ha : 0 < a) (hvols : (Ns : ℝ) * a = Ls)
    (G : AsymLatticeField Nt Ns)
    (γ rem C_rem_free C_free_assemble : ℝ) (hγ : γ < 1)
    (hPiece3 :
      ∫ ψ : ZMod Nt → SpatialField Ns,
          (asymSliceFamilyLinear ((asymSliceEquiv Nt Ns) G) ψ) ^ 2
          ∂((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt)
        ≤
      (2 / (1 - γ)) *
          groundSliceVarianceSum (Nt := Nt) (Ns := Ns) P a mass ha hmass
            ((asymSliceEquiv Nt Ns) G) + rem)
    (hRem :
      rem ≤ C_rem_free *
        freeSingleSliceCovarianceSum (Nt := Nt) (Ns := Ns) a mass ha hmass
          ((asymSliceEquiv Nt Ns) G))
    (hFreeAssemble :
      freeSingleSliceCovarianceSum (Nt := Nt) (Ns := Ns) a mass ha hmass
          ((asymSliceEquiv Nt Ns) G)
        ≤ C_free_assemble *
          ∫ ω : Configuration (AsymLatticeField Nt Ns), (ω G) ^ 2
            ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass))
    (hCoeff_nonneg :
      0 ≤ (2 / (1 - γ)) * groundVarianceFreeCovarianceConstant P mass hmass Ls hLs +
          C_rem_free) :
      ∫ ω : Configuration (AsymLatticeField Nt Ns), (ω G) ^ 2
          ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass)
        ≤
      (((2 / (1 - γ)) * groundVarianceFreeCovarianceConstant P mass hmass Ls hLs +
          C_rem_free) * C_free_assemble) *
        ∫ ω : Configuration (AsymLatticeField Nt Ns), (ω G) ^ 2
          ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by
  set C0 :=
    (2 / (1 - γ)) * groundVarianceFreeCovarianceConstant P mass hmass Ls hLs + C_rem_free
  have hsum :=
    interacting_second_moment_bound_to_freeCovariance_sum
      (Nt := Nt) (Ns := Ns) P mass hmass Ls hLs a ha hvols G
      γ rem C_rem_free hγ hPiece3 hRem
  calc
    ∫ ω : Configuration (AsymLatticeField Nt Ns), (ω G) ^ 2
        ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass)
        ≤ C0 *
          freeSingleSliceCovarianceSum (Nt := Nt) (Ns := Ns) a mass ha hmass
            ((asymSliceEquiv Nt Ns) G) := by
          simpa [C0] using hsum
    _ ≤ C0 *
          (C_free_assemble *
            ∫ ω : Configuration (AsymLatticeField Nt Ns), (ω G) ^ 2
              ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)) := by
          exact mul_le_mul_of_nonneg_left hFreeAssemble (by simpa [C0] using hCoeff_nonneg)
    _ = (C0 * C_free_assemble) *
          ∫ ω : Configuration (AsymLatticeField Nt Ns), (ω G) ^ 2
            ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by ring

end Pphi2

end
