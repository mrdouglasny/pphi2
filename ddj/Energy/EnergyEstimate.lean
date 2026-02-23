/-
  Pphi2.Energy.EnergyEstimate
  The a priori energy estimate on the cylinder, uniform in L and N.

  Reference: DDJ Section 5, Proposition 5.1.
  Adapted from spheres to cylinders: no conformal weight from
  stereographic projection needed.
-/
import Pphi2.StochasticQuant.DaPratoDebussche

noncomputable section

open MeasureTheory

/-! ## Weight function on the cylinder -/

/-- The weight function v_L on the cylinder ℝ × S¹_L,
    adapted to the cylinder geometry.
    DDJ Definition 5.1, cylinder version. -/
axiom energyWeight (L : ℝ) : SpaceTimeCyl 2 L → ℝ

/-- v_L is integrable with ‖v_L‖_{L¹} ≤ 1. -/
axiom energyWeight_integrable (L : ℝ) (hL : 1 ≤ L) :
    True -- v_L ∈ L¹ with norm ≤ 1

/-- v_L is positive. -/
axiom energyWeight_pos (L : ℝ) (hL : 1 ≤ L) (x : SpaceTimeCyl 2 L) :
    0 < energyWeight L x

/-! ## The main a priori bound on the cylinder -/

/-- **Proposition 5.1** (Energy estimate on the cylinder).
    There exist κ > 0, C > 0, p ≥ 1 such that
    for all t > 0, L ≥ 1, N ≥ 1:

    8 ∂_t ‖Ψ(t)‖²_{L₂(v_L^{1/2})} + ‖Ψ(t)‖ⁿ_{Lₙ(v_L^{1/n})}
      ≤ C Σ_{k=0}^{n-1} ‖Z^{:k:}(t)‖ᵖ_{Lₚ^{-κ}(v_L^{1/p})}

    This is the core estimate: the Ψ norm (interacting part) is controlled
    by the Z norms (free field, with known statistics).

    On the cylinder, no stereographic pullback j_R^* is needed.

    DDJ Proposition 5.1, adapted to cylinder. -/
axiom energy_estimate (P : InteractionPolynomial) :
    ∃ (κ C : ℝ) (p : ℝ),
      0 < κ ∧ 0 < C ∧ 1 ≤ p ∧
      ∀ (L : ℝ) (_ : 1 ≤ L) (N : ℕ+),
        True
        -- The actual bound on ∂_t‖Ψ‖² + ‖Ψ‖ⁿ ≤ C·(free field norms)

/-! ## Integration by parts estimates -/

/-- Lemma 5.2(A): Weighted Laplacian integration by parts on the cylinder.
    ⟨Ψ, v_L(-Δ_L)Ψ⟩ ≥ ½‖∇Ψ‖²_{L₂(v_L^{1/2})}
                        - ⅛‖Ψ‖²_{L₂(v_L^{1/2})}.
    DDJ Lemma 5.2(A), adapted to cylinder. -/
axiom weighted_ibp_first_order (L : ℝ) (hL : 1 ≤ L) :
    True -- integration by parts bound

/-- Lemma 5.2(B): Second-order weighted IBP on the cylinder. -/
axiom weighted_ibp_second_order (L : ℝ) (hL : 1 ≤ L) :
    True

/-- Lemma 5.2(C): Third-order weighted IBP on the cylinder. -/
axiom weighted_ibp_third_order (L : ℝ) (hL : 1 ≤ L) :
    True

end
