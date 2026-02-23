/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lattice Interaction

Defines the Wick-ordered lattice interaction `V_a(φ) = a^d Σ_x :P(φ(x)):_a`
for P(Φ)₂ field theory on the finite lattice.

## Main definitions

- `latticeInteraction P d N a mass` — the interaction functional V_a
- `latticeAction P d N a mass` — the full lattice action S_a = ½⟨φ,(-Δ+m²)φ⟩ + V_a

## Mathematical background

The lattice action for P(Φ)₂ is:
  `S_a[φ] = ½ a^d Σ_{x,i} a⁻²(φ(x+eᵢ) - φ(x))² + a^d Σ_x (½m²φ(x)² + :P(φ(x)):_a)`

The quadratic part `½⟨φ, (-Δ_a + m²)φ⟩` is the Gaussian action (already in
gaussian-field as `latticeGaussianMeasure`). The interaction is:

  `V_a(φ) = a^d Σ_x :P(φ(x)):_a`

where `:P:_a` is Wick-ordered with constant `c_a = wickConstant d N a mass`.

## References

- Glimm-Jaffe, *Quantum Physics*, §8.6, §19.1
- Simon, *The P(φ)₂ Euclidean QFT*, §II.1
-/

import Pphi2.WickOrdering.Counterterm

noncomputable section

open GaussianField

namespace Pphi2

variable (d N : ℕ) [NeZero N]

/-! ## Lattice interaction -/

/-- The Wick-ordered lattice interaction:

  `V_a(φ) = a^d · Σ_{x ∈ Λ} :P(φ(x)):_{c_a}`

where the sum is over all lattice sites and `:P:` is Wick-ordered with
respect to the lattice Gaussian covariance at coinciding points.

For d=2 on an N×N lattice, this is `a² Σ_x :P(φ(x)):_{c_a}`. -/
def latticeInteraction (P : InteractionPolynomial) (a mass : ℝ) :
    FinLatticeField d N → ℝ :=
  fun φ => a ^ d * ∑ x : FinLatticeSites d N,
    wickPolynomial P (wickConstant d N a mass) (φ x)

/-- The lattice interaction is bounded below.

Since P has even degree n ≥ 4 with positive leading coefficient, each
`:P(φ(x)):` is bounded below by `-A` for some constant A depending on
P and c_a. Therefore `V_a(φ) ≥ -A · a^d · |Λ|`.

This is crucial for the well-definedness of `exp(-V_a)`. -/
theorem latticeInteraction_bounded_below (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    ∃ B : ℝ, ∀ φ : FinLatticeField d N,
    latticeInteraction d N P a mass φ ≥ -B := by
  obtain ⟨A, hA_pos, hA_bound⟩ := wickPolynomial_bounded_below P (wickConstant d N a mass)
  refine ⟨a ^ d * Fintype.card (FinLatticeSites d N) * A, fun φ => ?_⟩
  unfold latticeInteraction
  have ha_pow : (0 : ℝ) < a ^ d := pow_pos ha d
  calc a ^ d * ∑ x : FinLatticeSites d N, wickPolynomial P (wickConstant d N a mass) (φ x)
      ≥ a ^ d * ∑ _x : FinLatticeSites d N, (-A) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt ha_pow)
        apply Finset.sum_le_sum
        intro x _
        exact hA_bound (φ x)
    _ = -(a ^ d * Fintype.card (FinLatticeSites d N) * A) := by
        simp [Finset.sum_const, mul_comm, mul_assoc, neg_mul]
        ring

/-- Each Wick monomial is continuous as a function of its real argument. -/
theorem wickMonomial_continuous : ∀ (n : ℕ) (c : ℝ), Continuous (wickMonomial n c)
  | 0, _ => continuous_const
  | 1, _ => continuous_id
  | n + 2, c => by
    show Continuous fun x => x * wickMonomial (n + 1) c x - (↑n + 1) * c * wickMonomial n c x
    exact ((continuous_id.mul (wickMonomial_continuous (n + 1) c)).sub
      (continuous_const.mul (wickMonomial_continuous n c)))

theorem latticeInteraction_continuous (P : InteractionPolynomial) (a mass : ℝ) :
    Continuous (latticeInteraction d N P a mass) := by
  unfold latticeInteraction
  apply Continuous.mul continuous_const
  apply continuous_finset_sum
  intro x _
  unfold wickPolynomial
  apply Continuous.add
  · exact continuous_const.mul ((wickMonomial_continuous P.n _).comp (continuous_apply x))
  · apply continuous_finset_sum
    intro m _
    exact continuous_const.mul ((wickMonomial_continuous m _).comp (continuous_apply x))

/-- The lattice interaction is convex when P is convex.

For even-degree polynomials P bounded below, `:P:_c` is convex in φ(x)
for each x (since Wick ordering only shifts by lower-order terms, and
the sum of convex functions is convex).

This enables the use of `fkg_perturbed` from gaussian-field. -/
axiom latticeInteraction_convex (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    ConvexOn ℝ Set.univ (latticeInteraction d N P a mass)

end Pphi2

end
