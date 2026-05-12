import Pphi2.NelsonEstimate.FieldDecomposition

noncomputable section

namespace Pphi2

open GaussianField

/-- **Glimm-Jaffe Thm 8.5.2 (smooth-side, d=2).**
Polylog `T` bound on the smooth Wick constant, uniform in `(N, a)` at fixed
`L = N * a`. -/
axiom smoothWickConstant_le_log_uniform_in_aN
    {d : ℕ} (hd : d = 2) (mass L : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a)
        (_h_vol : (N : ℝ) * a = L)
        (T : ℝ) (_hT : 0 < T),
        smoothWickConstant d N a mass T ≤ A + B * (1 + |Real.log T|)

/-- **Glimm-Jaffe Thm 8.5.2 (rough-side, d=2).**
Position-space `L^m` site-sum bound for the canonical rough covariance,
uniform in `(N, a)` at fixed `L = N * a`. -/
axiom canonicalRoughCovariance_pow_sum_le_uniform_in_aN
    {d : ℕ} (hd : d = 2) (mass L : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ C_m : ℝ, 0 < C_m ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a)
        (_h_vol : (N : ℝ) * a = L)
        (T : ℝ) (_hT : 0 < T) (x : FinLatticeSites d N),
        a^d * ∑ y : FinLatticeSites d N,
          |canonicalRoughCovariance d N a mass T x y| ^ m ≤ C_m * T

end Pphi2
