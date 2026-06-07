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

/-- **M2a — smooth interaction as a sum of diagonal cross-terms.** The smooth interaction is the
`j=k` (pure-smooth) part of the Wick expansion: `V_smooth = (1/P.n)·crossTerm(P.n,P.n) +
∑_m P.coeff m · crossTerm(m,m)`, where `canonicalCrossTerm k k = a^d ∑_x :φ_S(x)^k:` (the rough
factor `:φ_R^0: = 1`). Mirrors `canonicalRoughError_eq_sum_over_cross_terms` (which excludes `j=k`). -/
lemma canonicalSmoothInteraction_eq_sum_crossTerm_diag (d N : ℕ) [NeZero N] (a mass : ℝ)
    (T : ℝ) (P : InteractionPolynomial) (η : CanonicalJoint d N) :
    canonicalSmoothInteraction d N a mass T P η =
    (1 / P.n : ℝ) * canonicalCrossTerm d N a mass T η P.n P.n
    + ∑ m : Fin P.n, P.coeff m * canonicalCrossTerm d N a mass T η (m : ℕ) (m : ℕ) := by
  unfold canonicalSmoothInteraction canonicalCrossTerm
  simp only [Nat.sub_self, wickMonomial_zero, mul_one, wickPolynomial]
  rw [Finset.sum_add_distrib, mul_add]
  refine congr_arg₂ (· + ·) ?_ ?_
  · rw [← Finset.mul_sum]; ring
  · simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [mul_assoc, ← Finset.mul_sum]
    ring

/-- **M2c — per-term diagonal cross-term L² bound.** `∫ (crossTerm(k,k))² ≤ k!·C·(1+|log T|)^k`
uniform in `N`: the cross-term L² equals `(a^d)²·k!·∑_{x,y} C_smooth(x,y)^k`
(`canonicalCrossTerm_l2_sq_eq_covSum` at `j=k`, the rough factor being `C_rough^0 = 1`), and the
smooth double sum is bounded by M1. -/
theorem canonicalCrossTerm_diag_l2_sq_le {d : ℕ} (hd : d = 2) (mass L : ℝ)
    (hL : 0 < L) (hmass : 0 < mass) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a) (_hvol : (N : ℝ) * a = L)
      (T : ℝ) (_hT : 0 < T),
      ∫ η, (canonicalCrossTerm d N a mass T η k k) ^ 2 ∂(canonicalJointMeasure d N)
        ≤ (k.factorial : ℝ) * C * (1 + |Real.log T|) ^ k := by
  obtain ⟨C1, hC1, hM1⟩ := canonicalSmoothCovariance_pow_double_sum_le hd mass L hL hmass k
  refine ⟨C1, hC1, ?_⟩
  intro N _ a ha hvol T hT
  rw [canonicalCrossTerm_l2_sq_eq_covSum d N a mass ha hmass T hT k k]
  simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, mul_one, pow_zero]
  -- goal: a^d * a^d * k! * ∑_{x,y} C_smooth^k ≤ k! * C1 * (1+u)^k
  have habs : ∑ x : FinLatticeSites d N, ∑ y : FinLatticeSites d N,
        canonicalSmoothCovariance d N a mass T x y ^ k
      ≤ ∑ x : FinLatticeSites d N, ∑ y : FinLatticeSites d N,
        |canonicalSmoothCovariance d N a mass T x y| ^ k := by
    refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
    rw [← abs_pow]; exact le_abs_self _
  have hkfac : (0 : ℝ) ≤ (k.factorial : ℝ) := by positivity
  have hann : (0 : ℝ) ≤ a ^ d * a ^ d := by positivity
  calc a ^ d * a ^ d * (k.factorial : ℝ)
          * ∑ x : FinLatticeSites d N, ∑ y : FinLatticeSites d N,
            canonicalSmoothCovariance d N a mass T x y ^ k
      ≤ a ^ d * a ^ d * (k.factorial : ℝ)
          * ∑ x : FinLatticeSites d N, ∑ y : FinLatticeSites d N,
            |canonicalSmoothCovariance d N a mass T x y| ^ k :=
        mul_le_mul_of_nonneg_left habs (by positivity)
    _ = (k.factorial : ℝ) * (a ^ d * a ^ d * ∑ x : FinLatticeSites d N,
            ∑ y : FinLatticeSites d N, |canonicalSmoothCovariance d N a mass T x y| ^ k) := by ring
    _ ≤ (k.factorial : ℝ) * (C1 * (1 + |Real.log T|) ^ k) :=
        mul_le_mul_of_nonneg_left (hM1 N a ha hvol T hT) hkfac
    _ = (k.factorial : ℝ) * C1 * (1 + |Real.log T|) ^ k := by ring

end Pphi2
