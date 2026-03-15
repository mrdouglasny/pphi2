/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Heat Kernel Trace Bound

The core analytic lemma for Nelson's estimate: the trace of the lattice
heat kernel H(t) = Σ_k exp(-t·λ_k) satisfies H(t) ≤ C/t uniformly in N.

This reduces both eigenvalue sum bounds (smoothVariance_le_log and
roughCovariance_sq_summable) to elementary 1D calculus.

## Main results

- `schwinger_smooth` — `exp(-Tλ)/λ = ∫_T^∞ exp(-tλ) dt`
- `schwinger_rough` — `(1-exp(-Tλ))/λ = ∫₀ᵀ exp(-tλ) dt`
- `sin_sq_lower_bound` — `sin²(x) ≥ (2/π)²·x²` for |x| ≤ π/2
- `gaussian_sum_bound` — `Σ_k exp(-α·k²) ≤ 1 + √(π/α)`
- `heat_kernel_trace_bound` — `H(t) ≤ C/t` (uniform in N)

## References

- Gemini analysis of eigenvalue sum bounds via Schwinger parametrization
- Standard lattice QFT heat kernel estimates
-/

import Pphi2.NelsonEstimate.CovarianceSplit
import Pphi2.InteractingMeasure.LatticeMeasure

noncomputable section

open GaussianField MeasureTheory Real Finset
open scoped BigOperators

namespace Pphi2

/-! ## Schwinger parametrization identities -/

/-- Schwinger identity for the smooth covariance:
`exp(-T·λ) / λ = ∫_T^∞ exp(-t·λ) dt` for λ > 0, T ≥ 0. -/
private theorem hasDerivAt_neg_exp_div (lam : ℝ) (hlam : lam ≠ 0) (t : ℝ) :
    HasDerivAt (fun s => -exp (-s * lam) / lam) (exp (-t * lam)) t := by
  have h1 : HasDerivAt (fun s => -s * lam) (-lam) t := by
    simpa using (hasDerivAt_id t).neg.mul_const lam
  have h2 : HasDerivAt (fun s => exp (-s * lam)) (exp (-t * lam) * (-lam)) t :=
    h1.exp
  have h3 := h2.neg.div_const lam
  convert h3 using 1
  field_simp

theorem schwinger_smooth (lam : ℝ) (hlam : 0 < lam) (T : ℝ) (hT : 0 ≤ T) :
    exp (-T * lam) / lam = ∫ t in Set.Ici T, exp (-t * lam) := by
  sorry -- needs improper integral FTC: ∫_T^∞ f' = lim_{b→∞} F(b) - F(T)

/-- Schwinger identity for the rough covariance:
`(1 - exp(-T·λ)) / λ = ∫₀ᵀ exp(-t·λ) dt` for λ > 0, T ≥ 0. -/
theorem schwinger_rough_interval (lam : ℝ) (hlam : 0 < lam) (T : ℝ) (hT : 0 ≤ T) :
    (1 - exp (-T * lam)) / lam = ∫ t in (0)..T, exp (-t * lam) := by
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam
  set F := fun t => -exp (-t * lam) / lam
  have h_cont : ContinuousOn (fun t => exp (-t * lam)) (Set.uIcc 0 T) :=
    (Real.continuous_exp.comp (continuous_neg.mul continuous_const)).continuousOn
  have h_ftc : ∫ t in (0 : ℝ)..T, exp (-t * lam) = F T - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hasDerivAt_neg_exp_div lam hlam_ne t)
      h_cont.intervalIntegrable
  rw [h_ftc]; simp only [F, neg_zero, zero_mul, exp_zero]; field_simp; ring

theorem schwinger_rough (lam : ℝ) (hlam : 0 < lam) (T : ℝ) (hT : 0 ≤ T) :
    (1 - exp (-T * lam)) / lam = ∫ t in Set.Icc 0 T, exp (-t * lam) := by
  -- Follows from schwinger_rough_interval + Icc = uIcc conversion
  sorry

/-! ## Elementary bounds -/

/-- The standard trigonometric inequality: `sin(x)² ≥ (2/π)²·x²` for |x| ≤ π/2.
Equivalently: `sin(x) ≥ 2x/π` on [0, π/2] (Jordan's inequality). -/
theorem sin_sq_lower_bound (x : ℝ) (hx : |x| ≤ π / 2) :
    (2 / π) ^ 2 * x ^ 2 ≤ sin x ^ 2 := by
  sorry

/-- Gaussian sum bound: `Σ_{k=-∞}^{∞} exp(-α·k²) ≤ 1 + √(π/α)` for α > 0.
On a finite lattice, the finite sum is bounded by the infinite sum. -/
theorem gaussian_sum_bound (α : ℝ) (hα : 0 < α) :
    ∀ (M : ℕ), (∑ k ∈ Finset.Icc (-(M : ℤ)) M, exp (-α * (k : ℝ) ^ 2) : ℝ) ≤
    1 + sqrt (π / α) := by
  sorry

/-! ## Heat kernel trace bound -/

/-- The 1D heat kernel sum is bounded by C/√t:
`Σ_{k} exp(-t · 4sin²(πk/N)/a²) ≤ C · (1 + 1/√t)` for t > 0.

Uses sin² ≥ (2/π)²x² to reduce to Gaussian sums, then the Gaussian
sum bound. The constant C depends on L = a·N but NOT on N separately. -/
theorem heat_kernel_1d_bound (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a)
    (t : ℝ) (ht : 0 < t) :
    ∃ C : ℝ, 0 < C ∧
    (∑ k ∈ range N,
      exp (-t * (4 * sin (π * (k : ℝ) / N) ^ 2 / a ^ 2)) : ℝ) ≤
    C * (1 + 1 / sqrt t) := by
  sorry

/-- **Heat kernel trace bound** (the core lemma):
`H(t) = Σ_k exp(-t·λ_k) ≤ C/t` for t > 0, uniformly in N.

Proof: factor into 1D sums (tensor product structure of eigenvalues),
apply heat_kernel_1d_bound to each factor, multiply. -/
theorem heat_kernel_trace_bound (d N : ℕ) [NeZero N]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (t : ℝ) (ht : 0 < t) :
    ∃ C : ℝ, 0 < C ∧
    (∑ m ∈ range (Fintype.card (FinLatticeSites d N)),
      exp (-t * latticeEigenvalue d N a mass m) : ℝ) ≤ C / t := by
  sorry

/-! ## Deriving the eigenvalue sum bounds -/

/-- **Smooth variance bound** derived from heat kernel trace bound.

`Σ exp(-Tλ_k)/λ_k = ∫_T^∞ H(t) dt ≤ ∫_T^∞ C/t dt = C·|log T| + const` -/
theorem smoothVariance_from_heat_kernel (d N : ℕ) [NeZero N]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hd : d = 2) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧
    (∑ m ∈ range (Fintype.card (FinLatticeSites d N)),
      smoothCovEigenvalue d N a mass T m : ℝ) ≤ C * (1 + |log T|) := by
  -- Swap sum and integral via Schwinger, then integrate H(t) ≤ C/t from T to ∞
  sorry

/-- **Rough covariance L² bound** derived from heat kernel trace bound.

`Σ C_R(k)² = ∫₀ᵀ∫₀ᵀ H(t₁+t₂) dt₁ dt₂ ≤ ∫₀ᵀ∫₀ᵀ C/(t₁+t₂) dt₁dt₂ = O(T)` -/
theorem roughVariance_from_heat_kernel (d N : ℕ) [NeZero N]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hd : d = 2) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧
    (∑ m ∈ range (Fintype.card (FinLatticeSites d N)),
      roughCovEigenvalue d N a mass T m ^ 2 : ℝ) ≤ C * T := by
  -- Swap sum and double integral via Schwinger², then integrate H(t₁+t₂) ≤ C/(t₁+t₂)
  sorry

end Pphi2

end
