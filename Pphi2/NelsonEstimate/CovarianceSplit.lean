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
  sorry

/-! ## Variance bounds -/

/-- **Smooth variance bound**: The smooth Wick constant grows at most logarithmically in 1/T.

For d = 2 and T > 0: c_S ≤ C · (1 + |log T|)

The smooth covariance `exp(-T·λ_k)/λ_k` is exponentially suppressed for large λ_k,
so the sum over Fourier modes converges to O(|log T|) uniformly in N. -/
theorem smoothVariance_le_log (hd : d = 2) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ smoothWickConstant d N a mass T ≤ C * (1 + |Real.log T|) := by
  sorry

/-- **Rough covariance L² bound**: The sum of squared rough covariance eigenvalues
is O(T^δ) for some δ > 0, uniformly in N.

For d = 2: Σ_k C_R(k)² ≤ C · T^{1/2}

Uses: C_R(k) = (1-exp(-Tλ_k))/λ_k ≤ min(T, 1/λ_k), so
C_R(k)² ≤ T^{1/2} · λ_k^{-3/2}, and Σ λ_k^{-3/2} converges in d=2. -/
theorem roughCovariance_sq_summable (hd : d = 2) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧
    (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
    ∑ m ∈ range (Fintype.card (FinLatticeSites d N)),
      roughCovEigenvalue d N a mass T m ^ 2 ≤ C * T ^ (1/2 : ℝ) := by
  sorry

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
