/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.AsymTorus.AsymTransferKernelOperator
import Pphi2.AsymTorus.AsymGappedTransfer

/-!
# Layer-B2 trace bridge — connecting the kernel-iterate trace to the spectral gap

Bounds the dictionary's connected two-point `(Z)⁻¹∫∫ A·kPow_a·B·kPow_b` by the gap, discharging
the `Lt`-uniformity of `asymInteractingVariance_le_freeVariance_Lt_uniform` (and, by the same
machinery, the OS4 clustering axioms). With `asymTransferKernel_kPow_apply` (the operator↔kernel
link) in hand, this is **concrete Cauchy–Schwarz on explicit kernels**, not abstract trace-class
theory — see `docs/B4B5-design.md` §"HS trace-bridge — concrete construction".

## Two viable routes (update 2026-06-04)
pphi2 has **more spectral structure than the rank-1 picture needs**: `asymGroundVector` is a
`HilbertBasis` vector (so **‖Ω‖ = 1**), and `AsymJentzsch.lean:200` provides the **full Jentzsch
eigenbasis** — a complete `HilbertBasis ι ℝ (L2SpatialField Ns)` with eigenvalues. So BOTH engines
are usable: (i) the **rank-1** route (`connected_two_point_le`, the HS bricks below); (ii) the
**eigenbasis** route — `trace = Σ_{i:ι} ⟪b_i, · b_i⟫`, the spectral two-point expansion
`Σ_{k,l} |⟨b_k|M|b_l⟩|² λ_l^d λ_k^{Nt−d}`, fed to `averaged_susceptibility_bound` (proved). The norm
gap gives `λ_i ≤ γλ₀` for `i ≠ 0` (each `b_i ⊥ Ω`). Pick per tractability of the trace-class sum.

## Brick roadmap (this file) — rank-1/HS route
0. **Eigen-power** `T^{m+1} Ω = λ₀^{m+1} Ω` (this file, proved) — the foundation of the rank-1 split.
1. **Rank-1 kernel split** `kPow_m(x,y) = λ₀^{m+1}·Ω(x)Ω(y) + R_m(x,y)` (`R_m` = kernel of
   `T'^{m+1}`, `T' = T(1−P₀)`).  ← next
2. **R operator-norm decay** `‖T'^{m+1} f‖ ≤ (γλ₀)^{m+1}‖f‖` (= the proved gap, restated).
3. **Kernel Cauchy–Schwarz** on `L²(vol×vol)`.
4. **HS ≤ op·HS** for the `γ^a` geometric decay.
5. **Mixed `P₀·R` terms** via `connected_two_point_le` (reflection-positivity, proved).
6. **Assemble + normalize** → `geom_wrap_sum_le`.
-/

open MeasureTheory

namespace Pphi2

variable {Nt Ns : ℕ} [NeZero Nt] [NeZero Ns]

/-- The ground vector is an eigenvector of the (un-normalised) transfer operator with eigenvalue
`asymTransferGroundEigenvalue`. -/
theorem asymTransferOperatorCLM_groundVector (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    asymTransferOperatorCLM Nt Ns P a mass ha hmass (asymGroundVector Nt Ns P a mass ha hmass)
      = asymTransferGroundEigenvalue Nt Ns P a mass ha hmass •
          asymGroundVector Nt Ns P a mass ha hmass :=
  (asymTransferGroundExcitedData Nt Ns P a mass ha hmass).h_eigen _

/-- **Brick 0 — eigen-power.** `T^{m+1} Ω = λ₀^{m+1} Ω`. The foundation of the rank-1 split
`T^{m+1} = λ₀^{m+1} P₀ + T'^{m+1}`: it pins the `P₀` (vacuum) part of every kernel iterate. -/
theorem asymTransferOperatorCLM_pow_groundVector (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (m : ℕ) :
    ((asymTransferOperatorCLM Nt Ns P a mass ha hmass) ^ (m + 1))
        (asymGroundVector Nt Ns P a mass ha hmass)
      = (asymTransferGroundEigenvalue Nt Ns P a mass ha hmass) ^ (m + 1) •
          asymGroundVector Nt Ns P a mass ha hmass := by
  induction m with
  | zero => simp [pow_one, asymTransferOperatorCLM_groundVector]
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, ih, map_smul,
      asymTransferOperatorCLM_groundVector, smul_smul, ← pow_succ]

/-- `T = λ₀ • T̂` (un-normalised = eigenvalue × normalised). -/
theorem asymTransferOperatorCLM_eq_smul_normalized (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    asymTransferOperatorCLM Nt Ns P a mass ha hmass
      = asymTransferGroundEigenvalue Nt Ns P a mass ha hmass •
          asymTransferNormalized Nt Ns P a mass ha hmass := by
  rw [asymTransferNormalized, smul_smul,
    mul_inv_cancel₀ (ne_of_gt (asymTransferGroundEigenvalue_pos Nt Ns P a mass ha hmass)),
    one_smul]

/-- **Bricks 1+2 (decay).** On the vacuum-orthogonal complement, the un-normalised transfer
operator's powers decay geometrically at rate `γλ₀`: `‖T^{m+1} v‖ ≤ (γλ₀)^{m+1}‖v‖` for `v ⊥ Ω`.
This is the gap (`norm_T_pow_le` on the `GappedTransfer`) pushed through the `T = λ₀·T̂` rescaling —
the operator-norm decay that controls the connected (`R`) part of the kernel-iterate trace. -/
theorem asymTransferOperatorCLM_pow_norm_le_of_perp (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hnorm : ∀ v : L2SpatialField Ns,
      @inner ℝ _ _ (asymGroundVector Nt Ns P a mass ha hmass) v = 0 →
      ‖asymTransferNormalized Nt Ns P a mass ha hmass v‖ ≤ γ * ‖v‖)
    (m : ℕ) (v : L2SpatialField Ns)
    (hv : @inner ℝ _ _ (asymGroundVector Nt Ns P a mass ha hmass) v = 0) :
    ‖((asymTransferOperatorCLM Nt Ns P a mass ha hmass) ^ (m + 1)) v‖
      ≤ (γ * asymTransferGroundEigenvalue Nt Ns P a mass ha hmass) ^ (m + 1) * ‖v‖ := by
  have hpos := asymTransferGroundEigenvalue_pos Nt Ns P a mass ha hmass
  have hgap := (asymGappedTransfer Nt Ns P a mass ha hmass γ hγ0 hγ1 hnorm).norm_T_pow_le hv (m + 1)
  rw [asymTransferOperatorCLM_eq_smul_normalized, smul_pow, ContinuousLinearMap.smul_apply,
    norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hpos _), mul_pow]
  calc asymTransferGroundEigenvalue Nt Ns P a mass ha hmass ^ (m + 1) *
          ‖((asymTransferNormalized Nt Ns P a mass ha hmass) ^ (m + 1)) v‖
      ≤ asymTransferGroundEigenvalue Nt Ns P a mass ha hmass ^ (m + 1) * (γ ^ (m + 1) * ‖v‖) :=
        mul_le_mul_of_nonneg_left hgap (le_of_lt (pow_pos hpos _))
    _ = γ ^ (m + 1) * asymTransferGroundEigenvalue Nt Ns P a mass ha hmass ^ (m + 1) * ‖v‖ := by
        ring

end Pphi2
