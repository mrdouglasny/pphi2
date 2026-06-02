/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.AsymTorus.AsymPositivity
import ReflectionPositivity.TransferMatrix
import ReflectionPositivity.VarianceBound

/-!
# Asym cylinder transfer operator as a `GappedTransfer` (Layer B2, Part A)

Packages pphi2's spatial transfer operator `asymTransferOperatorCLM`
(self-adjoint, compact, with Perron-Frobenius ground state and mass gap)
as a `ReflectionPositivity.GappedTransfer`, so that the reusable
uniform-susceptibility bound `GappedTransfer.susceptibility_le` applies.

The operator is normalised to ground eigenvalue `1`
(`asymTransferNormalized`), and the vacuum is the Jentzsch ground vector
(`asymGroundVector`). Self-adjointness, vacuum invariance, and the gap
arithmetic are discharged here from pphi2's proved spectral lemmas.

The **operator-norm spectral gap** `‖T v‖ ≤ γ ‖v‖` on the
vacuum-orthogonal complement is taken as an explicit hypothesis
(`hnorm`): it requires the *true* spectral gap (sup of the non-ground
spectrum, attained via compactness), which is stronger than pphi2's
current `asymMassGap` (a gap to an arbitrary excited eigenvalue). See
`reflection-positivity/RECON.md` (op-1 plan) — establishing `hnorm` is
the remaining spectral lemma.
-/

open GaussianField Real MeasureTheory ReflectionPositivity

namespace Pphi2

variable (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
  (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)

/-- The Jentzsch ground eigenvector (vacuum) of the asym transfer operator. -/
noncomputable def asymGroundVector : L2SpatialField Ns :=
  (asymTransferGroundExcitedData Nt Ns P a mass ha hmass).b
    (asymTransferGroundExcitedData Nt Ns P a mass ha hmass).i₀

/-- The asym transfer operator normalised so the ground eigenvalue is `1`. -/
noncomputable def asymTransferNormalized :
    L2SpatialField Ns →L[ℝ] L2SpatialField Ns :=
  (asymTransferGroundEigenvalue Nt Ns P a mass ha hmass)⁻¹ •
    asymTransferOperatorCLM Nt Ns P a mass ha hmass

/-- The ground eigenvalue is strictly positive (Perron-Frobenius). -/
theorem asymTransferGroundEigenvalue_pos :
    0 < asymTransferGroundEigenvalue Nt Ns P a mass ha hmass :=
  asymTransferOperator_eigenvalues_pos Nt Ns P a mass ha hmass
    (asymTransferGroundExcitedData Nt Ns P a mass ha hmass).b
    (asymTransferGroundExcitedData Nt Ns P a mass ha hmass).eigenval
    (asymTransferGroundExcitedData Nt Ns P a mass ha hmass).h_eigen _

/-- **Part A**: package the (normalised) asym cylinder transfer operator
as a `GappedTransfer`, given the operator-norm spectral gap `hnorm`. The
uniform susceptibility bound `GappedTransfer.susceptibility_le` then
applies, giving the `Lt`-uniform variance bound (Layer B2). -/
noncomputable def asymGappedTransfer
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hnorm : ∀ v : L2SpatialField Ns,
      @inner ℝ _ _ (asymGroundVector Nt Ns P a mass ha hmass) v = 0 →
      ‖asymTransferNormalized Nt Ns P a mass ha hmass v‖ ≤ γ * ‖v‖) :
    GappedTransfer (L2SpatialField Ns) where
  T := asymTransferNormalized Nt Ns P a mass ha hmass
  vacuum := asymGroundVector Nt Ns P a mass ha hmass
  selfAdjoint x y := by
    have hsymm :=
      ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
        (asymTransferOperator_isSelfAdjoint Nt Ns P a mass ha hmass)
    simp only [asymTransferNormalized, ContinuousLinearMap.smul_apply,
      real_inner_smul_left, real_inner_smul_right]
    congr 1
    exact hsymm x y
  vacuum_eq := by
    have hpos := asymTransferGroundEigenvalue_pos Nt Ns P a mass ha hmass
    have hev : asymTransferOperatorCLM Nt Ns P a mass ha hmass
        (asymGroundVector Nt Ns P a mass ha hmass)
        = asymTransferGroundEigenvalue Nt Ns P a mass ha hmass •
            asymGroundVector Nt Ns P a mass ha hmass :=
      (asymTransferGroundExcitedData Nt Ns P a mass ha hmass).h_eigen _
    simp only [asymTransferNormalized, ContinuousLinearMap.smul_apply, hev, smul_smul,
      inv_mul_cancel₀ (ne_of_gt hpos), one_smul]
  gap := γ
  gap_nonneg := hγ0
  gap_lt_one := hγ1
  norm_le_of_orthogonal := hnorm

/-- **Layer B2 operator bound** via Part A: given the spectral gap
`hnorm`, the truncated two-point sum of the normalised transfer operator
against a vacuum-orthogonal observable `v` is bounded by `‖v‖²/(1−γ)`,
**uniformly in the number of time steps `N`** (hence in `Lt`). This is
`GappedTransfer.susceptibility_le` specialised to the asym cylinder. -/
theorem asymTransfer_susceptibility_le
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hnorm : ∀ v : L2SpatialField Ns,
      @inner ℝ _ _ (asymGroundVector Nt Ns P a mass ha hmass) v = 0 →
      ‖asymTransferNormalized Nt Ns P a mass ha hmass v‖ ≤ γ * ‖v‖)
    {v : L2SpatialField Ns}
    (hv : @inner ℝ _ _ (asymGroundVector Nt Ns P a mass ha hmass) v = 0) (N : ℕ) :
    ∑ n ∈ Finset.range N,
        |@inner ℝ _ _ v ((asymTransferNormalized Nt Ns P a mass ha hmass ^ n) v)|
      ≤ ‖v‖ ^ 2 / (1 - γ) :=
  (asymGappedTransfer Nt Ns P a mass ha hmass γ hγ0 hγ1 hnorm).susceptibility_le hv N

end Pphi2
