/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.NelsonEstimate.RoughErrorBound
import Pphi2.NelsonEstimate.CovarianceBoundsGJ
import Pphi2.InteractingMeasure.UniformBounds

/-!
# Uniform `L²` bound on the interaction (uniform-discharge brick L1) — smooth side

Toward `∫ V² dμ_GFF ≤ C(m,L)` uniform in `N` (`planning/L1-plan.md`). The bridge
`integral_interaction_sq_eq_canonicalJoint` and the rough variance `rough_error_variance` are done;
this file builds the **smooth** summability input (`M1`): the smooth covariance, being pointwise
bounded by `smoothWickConstant`, gives a trivial double-sum bound via `a^d·#sites = L^d` (no
row-sums needed, unlike the rough side).
-/

namespace Pphi2

open MeasureTheory GaussianField

/-- **M1 — smooth covariance double-sum bound.** Since `|C_smooth(x,y)| ≤ smoothWickConstant` (a
uniform `A + B(1+|log T|)`), the full double sum is controlled by the lattice volume squared:
`a^{2d} ∑_{x,y} |C_smooth(x,y)|^m ≤ C·(1+|log T|)^m`, uniform in `N` at fixed `L`. This is the
smooth-side summability input for the smooth interaction variance (M2). -/
theorem canonicalSmoothCovariance_pow_double_sum_le {d : ℕ} (hd : d = 2) (mass L : ℝ)
    (hL : 0 < L) (hmass : 0 < mass) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a) (_hvol : (N : ℝ) * a = L)
      (T : ℝ) (_hT : 0 < T),
      a ^ d * a ^ d * ∑ x : FinLatticeSites d N, ∑ y : FinLatticeSites d N,
        |canonicalSmoothCovariance d N a mass T x y| ^ m ≤ C * (1 + |Real.log T|) ^ m := by
  obtain ⟨A, B, hA, hB, hbd⟩ := smoothWickConstant_le_log_uniform_in_aN hd mass L hL hmass
  refine ⟨L ^ (2 * d) * (A + B) ^ m + 1, by positivity, ?_⟩
  intro N _ a ha hvol T hT
  set u := |Real.log T| with hudef
  have hu : 0 ≤ u := abs_nonneg _
  set S := smoothWickConstant d N a mass T with hSdef
  have hSbd : S ≤ A + B * (1 + u) := hbd N a ha hvol T hT
  have hSnn : 0 ≤ S :=
    le_trans (abs_nonneg _) (abs_canonicalSmoothCovariance_le_smoothWickConstant d N a mass ha hmass
      T hT (Classical.arbitrary _) (Classical.arbitrary _))
  -- termwise `|C_smooth x y|^m ≤ S^m`
  have hsum : ∑ x : FinLatticeSites d N, ∑ y : FinLatticeSites d N,
        |canonicalSmoothCovariance d N a mass T x y| ^ m
      ≤ ∑ _x : FinLatticeSites d N, ∑ _y : FinLatticeSites d N, S ^ m := by
    refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
    exact pow_le_pow_left₀ (abs_nonneg _)
      (abs_canonicalSmoothCovariance_le_smoothWickConstant d N a mass ha hmass T hT x y) m
  -- collapse the constant double sum to `card² · S^m` and use `a^d·card = L^d`
  have hcard : ∑ _x : FinLatticeSites d N, ∑ _y : FinLatticeSites d N, S ^ m
      = ((Fintype.card (FinLatticeSites d N) : ℝ)) ^ 2 * S ^ m := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hvold : a ^ d * (Fintype.card (FinLatticeSites d N) : ℝ) = L ^ d := by
    rw [lattice_volume_eq d N a]; congr 1; rw [mul_comm]; exact hvol
  -- `S^m ≤ (A+B(1+u))^m ≤ (A+B)^m (1+u)^m`
  have hSpow : S ^ m ≤ (A + B) ^ m * (1 + u) ^ m := by
    calc S ^ m ≤ (A + B * (1 + u)) ^ m := pow_le_pow_left₀ hSnn hSbd m
      _ ≤ ((A + B) * (1 + u)) ^ m := by
          refine pow_le_pow_left₀ (by positivity) ?_ m
          nlinarith [mul_nonneg hA hu, hu, hA, hB]
      _ = (A + B) ^ m * (1 + u) ^ m := mul_pow _ _ _
  have hsum2 : ∑ x : FinLatticeSites d N, ∑ y : FinLatticeSites d N,
        |canonicalSmoothCovariance d N a mass T x y| ^ m
      ≤ (Fintype.card (FinLatticeSites d N) : ℝ) ^ 2 * S ^ m := hsum.trans (le_of_eq hcard)
  calc a ^ d * a ^ d * ∑ x : FinLatticeSites d N, ∑ y : FinLatticeSites d N,
          |canonicalSmoothCovariance d N a mass T x y| ^ m
      ≤ a ^ d * a ^ d * ((Fintype.card (FinLatticeSites d N) : ℝ) ^ 2 * S ^ m) :=
        mul_le_mul_of_nonneg_left hsum2 (by positivity)
    _ = (L ^ d) ^ 2 * S ^ m := by
        rw [show a ^ d * a ^ d * ((Fintype.card (FinLatticeSites d N) : ℝ) ^ 2 * S ^ m)
          = (a ^ d * (Fintype.card (FinLatticeSites d N) : ℝ)) ^ 2 * S ^ m from by ring, hvold]
    _ ≤ (L ^ d) ^ 2 * ((A + B) ^ m * (1 + u) ^ m) :=
        mul_le_mul_of_nonneg_left hSpow (by positivity)
    _ ≤ (L ^ (2 * d) * (A + B) ^ m + 1) * (1 + u) ^ m := by
        have hLd : (L ^ d) ^ 2 = L ^ (2 * d) := by rw [← pow_mul, mul_comm]
        rw [hLd, add_mul, one_mul, ← mul_assoc]
        exact le_add_of_nonneg_right (by positivity)

end Pphi2
