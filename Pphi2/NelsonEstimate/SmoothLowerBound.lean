/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Classical Lower Bound for the Smooth Interaction

Shows that the smooth part of the Wick-ordered interaction (after covariance
splitting) is bounded below by a constant depending on log(1/T) but NOT on
the lattice size N.

## Main results

- `smooth_interaction_lower_bound` — `V_S(φ_S) ≥ -6L²·c_S²` for all φ_S
- `smooth_interaction_lower_bound_log` — `V_S(φ_S) ≥ -C·(1+|log T|)²`

## Mathematical content

After splitting φ = φ_S + φ_R with covariance C = C_S + C_R:

The smooth interaction V_S(φ_S) = a² Σ_x :φ_S(x)⁴:_{c_S} where
c_S = smoothWickConstant is the smooth Wick constant.

Since :x⁴:_c ≥ -6c² (from `wickMonomial_four_lower_bound`), we get:
  V_S(φ_S) ≥ a² · |Λ| · (-6c_S²) = -6L² · c_S²

The key point: this depends on c_S (which grows like log(1/T))
but NOT on N (since a²·|Λ| = L² is the physical volume).

## References

- Simon, *P(φ)₂ Euclidean QFT*, Chapter V, proof of Theorem V.12
-/

import Pphi2.NelsonEstimate.CovarianceSplit
import Pphi2.NelsonEstimate.WickBinomial

noncomputable section

open GaussianField MeasureTheory Finset
open scoped BigOperators

namespace Pphi2

variable (d N : ℕ) [NeZero N] (a mass : ℝ)

/-! ## Pointwise lower bound -/

/-- The Wick-ordered φ⁴ interaction at a single lattice site is bounded below:
`a^d · :φ(x)⁴:_c ≥ -6 · a^d · c²`

This is just `wickMonomial_four_lower_bound` scaled by the lattice spacing. -/
theorem site_interaction_lower_bound (ha : 0 < a) (c : ℝ) (hc : 0 ≤ c) (φx : ℝ) :
    -6 * a ^ d * c ^ 2 ≤ a ^ d * wickMonomial 4 c φx := by
  have ha_pow : 0 ≤ a ^ d := pow_nonneg ha.le d
  have := wickMonomial_four_lower_bound c hc φx
  nlinarith

/-! ## Summed lower bound -/

/-- The smooth interaction summed over all lattice sites is bounded below:
`V_S = a^d · Σ_x :φ_S(x)⁴:_{c_S} ≥ -6 · a^d · |Λ| · c_S²`

Since `a^d · |Λ| = L^d` (the physical volume), this is `-6 · L^d · c_S²`,
independent of N. -/
theorem smooth_interaction_lower_bound (ha : 0 < a)
    (c_S : ℝ) (hc_S : 0 ≤ c_S)
    (φ_S : FinLatticeSites d N → ℝ) :
    -(6 * a ^ d * (Fintype.card (FinLatticeSites d N) : ℝ) * c_S ^ 2) ≤
    a ^ d * ∑ x : FinLatticeSites d N, wickMonomial 4 c_S (φ_S x) := by
  -- Each site: a^d · :φ(x)⁴:_{c_S} ≥ -6 · a^d · c_S²
  have h_site : ∀ x : FinLatticeSites d N,
      -6 * c_S ^ 2 ≤ wickMonomial 4 c_S (φ_S x) :=
    fun x => wickMonomial_four_lower_bound c_S hc_S (φ_S x)
  -- Sum: Σ_x :φ(x)⁴: ≥ |Λ| · (-6c_S²)
  have h_sum : -(6 * (Fintype.card (FinLatticeSites d N) : ℝ) * c_S ^ 2) ≤
      ∑ x : FinLatticeSites d N, wickMonomial 4 c_S (φ_S x) := by
    calc ∑ x : FinLatticeSites d N, wickMonomial 4 c_S (φ_S x)
        ≥ ∑ _ : FinLatticeSites d N, (-6 * c_S ^ 2) :=
          Finset.sum_le_sum fun x _ => h_site x
      _ = (Fintype.card (FinLatticeSites d N) : ℝ) * (-6 * c_S ^ 2) := by
          simp [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ = _ := by ring
  -- Multiply by a^d ≥ 0
  have ha_pow : 0 ≤ a ^ d := pow_nonneg ha.le d
  nlinarith [mul_le_mul_of_nonneg_left h_sum ha_pow]

/-- **Volume-independent lower bound**: using `a^d · |Λ| = (a · N)^d = L^d`,
the lower bound depends only on L and c_S, not on N separately.

For the torus with spacing a = L/N: a^d · N^d = L^d. -/
theorem smooth_interaction_lower_bound_volume (ha : 0 < a)
    (L : ℝ) (hL : 0 < L) (ha_eq : a = L / N)
    (c_S : ℝ) (hc_S : 0 ≤ c_S)
    (φ_S : FinLatticeSites d N → ℝ) :
    -(6 * L ^ d * c_S ^ 2) ≤
    a ^ d * ∑ x : FinLatticeSites d N, wickMonomial 4 c_S (φ_S x) := by
  have h := smooth_interaction_lower_bound d N a ha c_S hc_S φ_S
  suffices hsuff : a ^ d * (Fintype.card (FinLatticeSites d N) : ℝ) = L ^ d by
    nlinarith
  -- a^d · |Λ| = (L/N)^d · N^d = L^d
  sorry -- lattice volume identity

/-! ## Combined with smooth variance bound -/

/-- **The classical lower bound for the smooth interaction** (Step 2 of Nelson's proof):

For the smooth interaction with Schwinger parameter T:
  V_S(φ_S) ≥ -C · (1 + |log T|)²

where C depends on L and mass but NOT on N.

Proof: combine `smooth_interaction_lower_bound` with `smoothVariance_le_log`. -/
theorem smooth_interaction_lower_bound_log (ha : 0 < a) (hmass : 0 < mass)
    (hd : d = 2) (L : ℝ) (hL : 0 < L) (ha_eq : a = L / N)
    (T : ℝ) (hT : 0 < T)
    (φ_S : FinLatticeSites d N → ℝ) :
    ∃ C : ℝ, 0 < C ∧
    -(C * (1 + |Real.log T|) ^ 2) ≤
    a ^ d * ∑ x : FinLatticeSites d N,
      wickMonomial 4 (smoothWickConstant d N a mass T) (φ_S x) := by
  -- Step 1: Get the smooth variance bound c_S ≤ K₁ · (1 + |log T|)
  obtain ⟨K₁, hK₁, h_cS_bound⟩ := smoothVariance_le_log d N a mass hd T hT
  -- Step 2: Apply smooth_interaction_lower_bound_volume
  -- V_S ≥ -6 L^d c_S² ≥ -6 L^d (K₁(1+|log T|))² = -6 L^d K₁² (1+|log T|)²
  have hc_S_nn : 0 ≤ smoothWickConstant d N a mass T := by
    sorry -- positivity of smoothWickConstant (sum of positive terms)
  have h_lower := smooth_interaction_lower_bound_volume d N a ha L hL ha_eq
    (smoothWickConstant d N a mass T) hc_S_nn φ_S
  refine ⟨6 * L ^ d * K₁ ^ 2, by positivity, ?_⟩
  -- Chain: -(6L²K₁²(1+|log T|)²) ≤ -(6L²c_S²) ≤ V_S
  have h_sq : (smoothWickConstant d N a mass T) ^ 2 ≤ (K₁ * (1 + |Real.log T|)) ^ 2 :=
    sq_le_sq' (by linarith [abs_nonneg (smoothWickConstant d N a mass T)]) h_cS_bound
  have hL_pow : 0 ≤ L ^ d := pow_nonneg hL.le d
  have : -(6 * L ^ d * K₁ ^ 2 * (1 + |Real.log T|) ^ 2) ≤
      -(6 * L ^ d * smoothWickConstant d N a mass T ^ 2) := by
    apply neg_le_neg
    calc 6 * L ^ d * smoothWickConstant d N a mass T ^ 2
        ≤ 6 * L ^ d * (K₁ * (1 + |Real.log T|)) ^ 2 :=
          mul_le_mul_of_nonneg_left h_sq (by positivity)
      _ = 6 * L ^ d * K₁ ^ 2 * (1 + |Real.log T|) ^ 2 := by ring
  linarith

end Pphi2

end
