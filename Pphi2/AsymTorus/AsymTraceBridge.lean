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

## Brick roadmap (this file)
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

end Pphi2
