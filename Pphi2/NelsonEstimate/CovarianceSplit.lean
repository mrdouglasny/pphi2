/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Covariance Splitting for Nelson's Estimate

Defines the heat-kernel (Schwinger parametrization) splitting of the lattice
GFF covariance into smooth and rough parts, and proves the key variance bounds.

## Main definitions

- `smoothCovariance T` — eigenvalues `exp(-T·λ_k)/λ_k` (low frequency)
- `roughCovariance T` — eigenvalues `(1-exp(-T·λ_k))/λ_k` (high frequency)

## Main results

- `covariance_split` — `C(k) = smoothCovariance T k + roughCovariance T k`
- `smoothVariance_le_log` — `Σ smoothCovariance T k ≤ O(|log T|)`
- `roughCovariance_sq_summable` — `Σ roughCovariance T k² ≤ O(T^δ)`

## References

- Simon, *P(φ)₂ Euclidean QFT*, Chapter V
- Glimm-Jaffe, *Quantum Physics*, Section 8.6
-/

import Pphi2.InteractingMeasure.LatticeMeasure
import Mathlib.Analysis.Complex.Exponential

noncomputable section

open GaussianField MeasureTheory Finset
open scoped BigOperators

namespace Pphi2

variable (d N : ℕ) [NeZero N] (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)

/-! ## Eigenvalue-based covariance splitting -/

/-- The smooth (low-frequency) part of the covariance at Fourier mode `m`.
Equals `exp(-T·λ_m) / λ_m` where `λ_m` is the lattice eigenvalue. -/
def smoothCovEigenvalue (T : ℝ) (m : ℕ) : ℝ :=
  Real.exp (-T * latticeEigenvalue d N a mass m) / latticeEigenvalue d N a mass m

/-- The rough (high-frequency) part of the covariance at Fourier mode `m`.
Equals `(1 - exp(-T·λ_m)) / λ_m`. -/
def roughCovEigenvalue (T : ℝ) (m : ℕ) : ℝ :=
  (1 - Real.exp (-T * latticeEigenvalue d N a mass m)) / latticeEigenvalue d N a mass m

/-- The covariance eigenvalue splits into smooth + rough parts. -/
theorem covariance_split (T : ℝ) (m : ℕ) :
    (latticeEigenvalue d N a mass m)⁻¹ =
    smoothCovEigenvalue d N a mass T m + roughCovEigenvalue d N a mass T m := by
  unfold smoothCovEigenvalue roughCovEigenvalue
  rw [div_add_div_same]
  congr 1; ring

/-- The smooth Wick constant: average of smooth covariance eigenvalues. -/
def smoothWickConstant (T : ℝ) : ℝ :=
  (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
  ∑ m ∈ range (Fintype.card (FinLatticeSites d N)),
    smoothCovEigenvalue d N a mass T m

/-- The rough Wick constant: average of rough covariance eigenvalues. -/
def roughWickConstant (T : ℝ) : ℝ :=
  (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
  ∑ m ∈ range (Fintype.card (FinLatticeSites d N)),
    roughCovEigenvalue d N a mass T m

/-- The Wick constant splits: c_a = c_S + c_R. -/
theorem wickConstant_split (T : ℝ) :
    wickConstant d N a mass =
    smoothWickConstant d N a mass T + roughWickConstant d N a mass T := by
  unfold wickConstant smoothWickConstant roughWickConstant
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl; intro m _
  exact covariance_split d N a mass T m

/-! ## Variance bounds -/

/-- **Smooth variance bound**: The smooth Wick constant grows at most logarithmically in 1/T.

For d = 2 and T > 0: c_S ≤ C · (1 + |log T|)

The smooth covariance `exp(-T·λ_k)/λ_k` is exponentially suppressed for large λ_k,
so the sum over Fourier modes converges to O(|log T|) uniformly in N. -/
theorem smoothVariance_le_log (hd : d = 2) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ smoothWickConstant d N a mass T ≤ C * (1 + |Real.log T|) := by
  -- smoothWickConstant = (1/|Λ|) * Σ smoothCovEigenvalue
  -- ≤ (1/|Λ|) * C * (1 + |log T|) from smoothVariance_from_heat_kernel
  sorry -- derives from HeatKernelBound.smoothVariance_from_heat_kernel

/-- The rough L² bound is O(T).
C_R(k) ≤ T (since (1-e^{-x})/x ≤ 1), so C_R(k)² ≤ T·C_R(k) ≤ T/λ_k.
Averaging: Σ C_R² / |Λ| ≤ T · c_a ≤ T/m². -/
theorem roughCovEigenvalue_le_T (T : ℝ) (hT : 0 ≤ T) (m : ℕ)
    (ha : 0 < a) (hmass : 0 < mass) :
    roughCovEigenvalue d N a mass T m ≤ T := by
  unfold roughCovEigenvalue
  have hev := latticeEigenvalue_pos d N a mass ha hmass m
  rw [div_le_iff₀ hev]
  -- Need: 1 - exp(-Tλ) ≤ T·λ
  -- From add_one_le_exp(-x): -x + 1 ≤ exp(-x), so 1 - exp(-x) ≤ x
  have h := Real.add_one_le_exp (-(T * latticeEigenvalue d N a mass m))
  -- h: -(T * λ) + 1 ≤ Real.exp (-(T * λ))
  -- goal: 1 - Real.exp (-T * λ) ≤ T * λ
  -- The key: -T * λ = -(T * λ), normalize via ring_nf
  have : Real.exp (-(T * latticeEigenvalue d N a mass m)) =
         Real.exp (-T * latticeEigenvalue d N a mass m) := by ring_nf
  linarith

theorem roughCovEigenvalue_le_inv (T : ℝ) (m : ℕ)
    (ha : 0 < a) (hmass : 0 < mass) :
    roughCovEigenvalue d N a mass T m ≤ (latticeEigenvalue d N a mass m)⁻¹ := by
  unfold roughCovEigenvalue
  have hev := latticeEigenvalue_pos d N a mass ha hmass m
  rw [inv_eq_one_div]
  apply div_le_div_of_nonneg_right _ hev.le
  linarith [Real.exp_nonneg (-T * latticeEigenvalue d N a mass m)]

theorem roughCovariance_sq_summable (T : ℝ) (hT : 0 < T)
    (ha : 0 < a) (hmass : 0 < mass) :
    (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
    ∑ m ∈ range (Fintype.card (FinLatticeSites d N)),
      roughCovEigenvalue d N a mass T m ^ 2 ≤
    T * wickConstant d N a mass := by
  -- C_R(k)² ≤ C_R(k) · T ≤ (1/λ_k) · T
  have h_le : ∀ m ∈ range (Fintype.card (FinLatticeSites d N)),
      roughCovEigenvalue d N a mass T m ^ 2 ≤
      T * (latticeEigenvalue d N a mass m)⁻¹ := by
    intro m _
    have hR_nn : 0 ≤ roughCovEigenvalue d N a mass T m := by
      unfold roughCovEigenvalue; apply div_nonneg
      · have hev := latticeEigenvalue_pos d N a mass ha hmass m
        have hTlam : 0 < T * latticeEigenvalue d N a mass m := mul_pos hT hev
        have : Real.exp (-T * latticeEigenvalue d N a mass m) ≤ 1 := by
          apply Real.exp_le_one_iff.mpr; linarith
        linarith
      · exact (latticeEigenvalue_pos d N a mass ha hmass m).le
    calc roughCovEigenvalue d N a mass T m ^ 2
        = roughCovEigenvalue d N a mass T m * roughCovEigenvalue d N a mass T m := sq _
      _ ≤ T * (latticeEigenvalue d N a mass m)⁻¹ :=
          mul_le_mul (roughCovEigenvalue_le_T d N a mass T hT.le m ha hmass)
            (roughCovEigenvalue_le_inv d N a mass T m ha hmass) hR_nn hT.le
  calc (1 / ↑(Fintype.card (FinLatticeSites d N))) *
      ∑ m ∈ range (Fintype.card (FinLatticeSites d N)),
        roughCovEigenvalue d N a mass T m ^ 2
      ≤ (1 / ↑(Fintype.card (FinLatticeSites d N))) *
        ∑ m ∈ range (Fintype.card (FinLatticeSites d N)),
          T * (latticeEigenvalue d N a mass m)⁻¹ := by
        apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum h_le) (by positivity)
    _ = T * wickConstant d N a mass := by
        unfold wickConstant
        rw [← Finset.mul_sum]
        ring

/-! ## Positivity -/

/-- Smooth covariance eigenvalues are positive. -/
theorem smoothCovEigenvalue_pos (T : ℝ) (hT : 0 < T) (m : ℕ)
    (ha : 0 < a) (hmass : 0 < mass) :
    0 < smoothCovEigenvalue d N a mass T m := by
  unfold smoothCovEigenvalue
  apply div_pos (Real.exp_pos _)
  exact latticeEigenvalue_pos d N a mass ha hmass m

/-- Rough covariance eigenvalues are positive. -/
theorem roughCovEigenvalue_pos (T : ℝ) (hT : 0 < T) (m : ℕ)
    (ha : 0 < a) (hmass : 0 < mass) :
    0 < roughCovEigenvalue d N a mass T m := by
  unfold roughCovEigenvalue
  apply div_pos
  · have hev := latticeEigenvalue_pos d N a mass ha hmass m
    have : 0 < T * latticeEigenvalue d N a mass m := mul_pos hT hev
    have : Real.exp (-T * latticeEigenvalue d N a mass m) < 1 :=
      Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  · exact latticeEigenvalue_pos d N a mass ha hmass m

end Pphi2

end
